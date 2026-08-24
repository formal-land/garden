//! Deterministic differential fixtures for the Post-NU6.3 Orchard proof verifier.

use ff::{Field, PrimeField};
use group::{Curve, Group, GroupEncoding};
use halo2_proofs::plonk::Error;
use orchard::{
    builder::{Builder, BundleType},
    bundle::{BundleVersion, Flags},
    circuit::{Instance, OrchardCircuitVersion, ProvingKey, VerifyingKey},
    tree::Anchor,
    Proof,
};
use pasta_curves::{
    arithmetic::{Coordinates, CurveAffine},
    pallas,
};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    panic::{catch_unwind, AssertUnwindSafe},
    path::{Path, PathBuf},
    process::Command,
};

const SCHEMA_VERSION: u32 = 1;
const CHUNK_BYTES: usize = 32;
const EXPECTED_CASES: usize = 40;
const EXPECTED_COVERAGE_IDS: usize = 44;
const PINNED_RUST_TARGET: &str = "x86_64-unknown-linux-gnu";
const ORCHARD_PIN: &str = "05d899241b7a907d9c47dc5d3d7b3aa1361d785c";
const HALO2_PIN: &str = "cca1dd70c5ac76daa7d9773eb9a26e33ceea9a6a";
const ROCQ_OF_RUST_PIN: &str = "dbb90c1e3dc76707bba73f8cd10ead38790c808d";
const PINNED_SUBMODULES: &[(&str, &str)] = &[
    ("third-party/orchard", ORCHARD_PIN),
    ("third-party/halo2", HALO2_PIN),
    ("third-party/rocq-of-rust", ROCQ_OF_RUST_PIN),
];
const REQUIRED_COVERAGE: &[&str] = &[
    "verified",
    "one_action",
    "two_actions",
    "restricted_flag",
    "unrestricted_flag",
    "spends_disabled_flag",
    "outputs_disabled_flag",
    "two_action_rejection",
    "trailing_bytes",
    "instance_binding",
    "zero_proofs",
    "canonical_scalar_tamper",
    "transcript_scalar_decode",
    "transcript_point_decode",
    "transcript_identity_rejection",
    "permutation_eval_desync",
    "multiopen_u",
    "ipa_round",
    "ipa_final",
    "constraint_system_failure",
    "opening",
    "truncated_stream",
    "empty",
    "partial_first_point",
    "after_advice_commitments",
    "after_lookup_permuted",
    "after_permutation_products",
    "after_lookup_products",
    "after_random_commitment",
    "after_quotient_pieces",
    "after_instance_evals",
    "after_advice_evals",
    "after_fixed_evals",
    "after_random_eval",
    "after_permutation_common",
    "inside_permutation_sets",
    "after_permutation_sets",
    "after_lookup_evals",
    "after_q_prime",
    "after_multiopen_u",
    "after_s_commitment",
    "inside_ipa_rounds",
    "before_ipa_c",
    "before_ipa_f",
];

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct SourcePins {
    orchard: String,
    halo2: String,
    rocq_of_rust: String,
    rust_target: String,
    usize_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct Shape {
    circuit: String,
    k: u32,
    instance_width: usize,
    proof_base_bytes: usize,
    proof_bytes_per_action: usize,
    advice_queries: usize,
    fixed_queries: usize,
    permutation_columns: usize,
    permutation_sets: usize,
    lookups: usize,
    quotient_pieces: usize,
    multiopen_point_sets: usize,
    ipa_rounds: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct ProofSnapshot {
    id: String,
    seed_byte: u8,
    num_actions: usize,
    cross_address_enabled: bool,
    proof_hex: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct InputSnapshot {
    id: String,
    /// One ten-scalar column for every proof in the aggregated Halo2 proof.
    instances_le_hex: Vec<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum ProofMutation {
    Identity,
    Append { hex: String },
    Truncate { len: usize },
    ReplaceChunk { index: usize, hex: String },
    RemoveChunk { index: usize },
    IncrementScalar { index: usize },
    FlipPointSign { index: usize },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum OutcomeKind {
    Verified,
    Rejected,
    Panicked,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct VerifyOutcome {
    kind: OutcomeKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    detail: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct CaseSnapshot {
    id: String,
    proof: String,
    inputs: String,
    mutation: ProofMutation,
    rust_outcome: VerifyOutcome,
    covers: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct CoverageEntry {
    id: String,
    cases: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct Snapshot {
    schema_version: u32,
    source: SourcePins,
    shape: Shape,
    proofs: Vec<ProofSnapshot>,
    inputs: Vec<InputSnapshot>,
    cases: Vec<CaseSnapshot>,
    branch_coverage: Vec<CoverageEntry>,
}

struct GeneratedProof {
    proof: ProofSnapshot,
    input: InputSnapshot,
    rust_instances: Vec<Instance>,
}

fn fixture_rng(seed: u8) -> ChaCha20Rng {
    ChaCha20Rng::from_seed([seed; 32])
}

fn git_output(repository: &Path, args: &[&str]) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repository)
        .args(args)
        .output()
        .map_err(|error| format!("could not run git in {}: {error}", repository.display()))?;
    if !output.status.success() {
        return Err(format!(
            "git {} failed in {}: {}",
            args.join(" "),
            repository.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| format!("git output was not UTF-8: {error}"))
}

fn verify_pinned_submodules() -> Result<(), String> {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("could not locate the Garden repository: {error}"))?;

    for (path, expected) in PINNED_SUBMODULES {
        let index = git_output(&repository, &["ls-files", "--stage", "--", path])?;
        let entries = index.lines().collect::<Vec<_>>();
        if entries.len() != 1 {
            return Err(format!(
                "expected one index gitlink for {path}, found {}",
                entries.len()
            ));
        }
        let fields = entries[0].split_whitespace().collect::<Vec<_>>();
        if fields.len() != 4
            || fields[0] != "160000"
            || fields[1] != *expected
            || fields[2] != "0"
            || fields[3] != *path
        {
            return Err(format!(
                "index gitlink for {path} is {:?}, expected mode 160000 at {expected}",
                entries[0]
            ));
        }

        let checkout = repository.join(path);
        let head = git_output(&checkout, &["rev-parse", "HEAD"])?;
        if head.trim() != *expected {
            return Err(format!(
                "initialized {path} HEAD is {}, expected {expected}",
                head.trim()
            ));
        }
        let dirty = git_output(
            &checkout,
            &[
                "status",
                "--porcelain=v1",
                "--untracked-files=all",
                "--ignore-submodules=none",
            ],
        )?;
        if !dirty.is_empty() {
            return Err(format!(
                "initialized {path} checkout is dirty:\n{}",
                dirty.trim_end()
            ));
        }
    }
    Ok(())
}

fn version_and_flags(cross_address_enabled: bool) -> (BundleVersion, Flags) {
    if cross_address_enabled {
        // Ironwood V3 permits either flag value and uses the same Post-NU6.3 action circuit.
        (BundleVersion::ironwood_v3(), Flags::ENABLED)
    } else {
        (BundleVersion::orchard_v3(), Flags::CROSS_ADDRESS_DISABLED)
    }
}

fn build_unproven(
    seed: u8,
    num_actions: usize,
    cross_address_enabled: bool,
) -> Result<
    orchard::Bundle<
        orchard::builder::InProgress<orchard::builder::Unproven, orchard::builder::Unauthorized>,
        i64,
    >,
    String,
> {
    let (version, flags) = version_and_flags(cross_address_enabled);
    build_unproven_with_flags(seed, num_actions, version, flags)
}

fn build_unproven_with_flags(
    seed: u8,
    num_actions: usize,
    version: BundleVersion,
    flags: Flags,
) -> Result<
    orchard::Bundle<
        orchard::builder::InProgress<orchard::builder::Unproven, orchard::builder::Unauthorized>,
        i64,
    >,
    String,
> {
    let builder = Builder::new(
        BundleType::Transactional {
            bundle_required: true,
            pad_to_minimum: Some(
                u8::try_from(num_actions).map_err(|_| "action count exceeds u8".to_owned())?,
            ),
        },
        version,
        flags,
        Anchor::empty_tree(),
    )
    .map_err(|error| format!("builder construction failed: {error:?}"))?;

    let mut rng = fixture_rng(seed);
    builder
        .build::<i64>(&mut rng)
        .map_err(|error| format!("bundle construction failed: {error:?}"))?
        .map(|(bundle, _)| bundle)
        .ok_or_else(|| "the required fixture bundle was omitted".to_owned())
}

fn scalar_hex(bytes: [u8; 32]) -> String {
    hex::encode(bytes)
}

fn point_coordinates(bytes: [u8; 32]) -> Result<([u8; 32], [u8; 32]), String> {
    let point = Option::<pallas::Point>::from(pallas::Point::from_bytes(&bytes))
        .ok_or_else(|| "Orchard action contains a non-canonical Pallas point".to_owned())?;
    if bool::from(point.is_identity()) {
        return Ok((pallas::Base::ZERO.to_repr(), pallas::Base::ZERO.to_repr()));
    }
    let affine = point.to_affine();
    let coordinates: Coordinates<pallas::Affine> = Option::from(affine.coordinates())
        .ok_or_else(|| "non-identity Pallas point has no affine coordinates".to_owned())?;
    Ok((coordinates.x().to_repr(), coordinates.y().to_repr()))
}

fn serialize_instances<T>(
    bundle: &orchard::Bundle<T, i64>,
) -> Result<(Vec<Instance>, Vec<Vec<String>>), String>
where
    T: orchard::bundle::Authorization,
{
    let flags = *bundle.flags();
    let anchor = *bundle.anchor();
    let mut rust_instances = Vec::with_capacity(bundle.actions().len());
    let mut encoded = Vec::with_capacity(bundle.actions().len());

    for action in bundle.actions().iter() {
        rust_instances.push(action.to_instance(flags, anchor));

        let (cv_x, cv_y) = point_coordinates(action.cv_net().to_bytes())?;
        let rk_bytes: [u8; 32] = action.rk().clone().into();
        let (rk_x, rk_y) = point_coordinates(rk_bytes)?;
        let bit = |value: bool| {
            let mut bytes = [0u8; 32];
            bytes[0] = u8::from(value);
            scalar_hex(bytes)
        };

        encoded.push(vec![
            scalar_hex(anchor.to_bytes()),
            scalar_hex(cv_x),
            scalar_hex(cv_y),
            scalar_hex(action.nullifier().to_bytes()),
            scalar_hex(rk_x),
            scalar_hex(rk_y),
            scalar_hex(action.cmx().to_bytes()),
            bit(flags.spends_enabled()),
            bit(flags.outputs_enabled()),
            bit(!flags.cross_address_enabled()),
        ]);
    }

    Ok((rust_instances, encoded))
}

fn generate_proof(
    seed: u8,
    num_actions: usize,
    cross_address_enabled: bool,
    id: &str,
    pk: &ProvingKey,
    vk: &VerifyingKey,
) -> Result<GeneratedProof, String> {
    let unproven = build_unproven(seed, num_actions, cross_address_enabled)?;
    let (rust_instances, encoded) = serialize_instances(&unproven)?;
    let mut rng = fixture_rng(seed);
    // The fixture exporter in Orchard uses the same RNG for construction and proving. Rebuild the
    // bundle while retaining that continuous RNG stream so these bytes match the upstream capture.
    let (version, flags) = version_and_flags(cross_address_enabled);
    let builder = Builder::new(
        BundleType::Transactional {
            bundle_required: true,
            pad_to_minimum: Some(u8::try_from(num_actions).unwrap()),
        },
        version,
        flags,
        Anchor::empty_tree(),
    )
    .map_err(|error| format!("builder construction failed: {error:?}"))?;
    let bundle = builder
        .build::<i64>(&mut rng)
        .map_err(|error| format!("bundle construction failed: {error:?}"))?
        .map(|(bundle, _)| bundle)
        .ok_or_else(|| "the required fixture bundle was omitted".to_owned())?;
    let (continuous_instances, continuous_encoded) = serialize_instances(&bundle)?;
    let authorized = bundle
        .create_proof(pk, &mut rng)
        .map_err(|error| format!("proof creation failed: {error:?}"))?
        .apply_signatures(&mut rng, [0; 32], &[])
        .map_err(|error| format!("signature application failed: {error:?}"))?;
    let rust_proof = authorized.authorization().proof().clone();
    let actual = verify_outcome(&rust_proof, vk, &continuous_instances);
    if actual.kind != OutcomeKind::Verified {
        return Err(format!("fresh fixture {id} did not verify: {actual:?}"));
    }

    // The independently rebuilt input confirms that public inputs depend only on the seeded bundle
    // construction, not on proof generation.
    if encoded != continuous_encoded || rust_instances.len() != continuous_instances.len() {
        return Err("deterministic fixture reconstruction produced different instances".to_owned());
    }

    let bytes = rust_proof.as_ref();
    let expected = Proof::expected_proof_size(num_actions);
    if bytes.len() != expected {
        return Err(format!(
            "proof length mismatch for {id}: got {}, expected {expected}",
            bytes.len()
        ));
    }

    Ok(GeneratedProof {
        proof: ProofSnapshot {
            id: id.to_owned(),
            seed_byte: seed,
            num_actions,
            cross_address_enabled,
            proof_hex: hex::encode(bytes),
        },
        input: InputSnapshot {
            id: format!("{id}_inputs"),
            instances_le_hex: continuous_encoded,
        },
        rust_instances: continuous_instances,
    })
}

fn generate_inputs_only(
    seed: u8,
    num_actions: usize,
    cross_address_enabled: bool,
    id: &str,
) -> Result<(InputSnapshot, Vec<Instance>), String> {
    let (version, flags) = version_and_flags(cross_address_enabled);
    generate_inputs_only_with_flags(seed, num_actions, version, flags, id)
}

fn generate_inputs_only_with_flags(
    seed: u8,
    num_actions: usize,
    version: BundleVersion,
    flags: Flags,
    id: &str,
) -> Result<(InputSnapshot, Vec<Instance>), String> {
    let bundle = build_unproven_with_flags(seed, num_actions, version, flags)?;
    let (instances, encoded) = serialize_instances(&bundle)?;
    Ok((
        InputSnapshot {
            id: id.to_owned(),
            instances_le_hex: encoded,
        },
        instances,
    ))
}

fn panic_detail(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_owned()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "non-string panic payload".to_owned()
    }
}

fn verify_outcome(proof: &Proof, vk: &VerifyingKey, instances: &[Instance]) -> VerifyOutcome {
    match catch_unwind(AssertUnwindSafe(|| proof.verify(vk, instances))) {
        Ok(Ok(())) => VerifyOutcome {
            kind: OutcomeKind::Verified,
            error: None,
            detail: None,
        },
        Ok(Err(error)) => {
            let (name, detail) = match error {
                Error::InvalidInstances => ("invalid_instances", None),
                Error::InstanceTooLarge => ("instance_too_large", None),
                Error::Transcript(error) => ("transcript", Some(error.to_string())),
                Error::Opening => ("opening", None),
                Error::ConstraintSystemFailure => ("constraint_system_failure", None),
                other => ("other", Some(format!("{other:?}"))),
            };
            VerifyOutcome {
                kind: OutcomeKind::Rejected,
                error: Some(name.to_owned()),
                detail,
            }
        }
        Err(payload) => VerifyOutcome {
            kind: OutcomeKind::Panicked,
            error: None,
            detail: Some(panic_detail(payload)),
        },
    }
}

fn mutation_bytes(proof: &ProofSnapshot, mutation: &ProofMutation) -> Result<Vec<u8>, String> {
    let mut bytes = hex::decode(&proof.proof_hex)
        .map_err(|error| format!("invalid proof hex for {}: {error}", proof.id))?;
    let chunk_range = |index: usize, len: usize| -> Result<std::ops::Range<usize>, String> {
        let start = index
            .checked_mul(CHUNK_BYTES)
            .ok_or_else(|| "proof chunk offset overflow".to_owned())?;
        let end = start
            .checked_add(CHUNK_BYTES)
            .ok_or_else(|| "proof chunk end overflow".to_owned())?;
        if end > len {
            return Err(format!("proof chunk {index} is outside {len} bytes"));
        }
        Ok(start..end)
    };

    match mutation {
        ProofMutation::Identity => {}
        ProofMutation::Append { hex } => {
            bytes.extend(hex::decode(hex).map_err(|error| format!("invalid append hex: {error}"))?)
        }
        ProofMutation::Truncate { len } => {
            if *len > bytes.len() {
                return Err(format!("cannot truncate {} bytes to {len}", bytes.len()));
            }
            bytes.truncate(*len);
        }
        ProofMutation::ReplaceChunk { index, hex } => {
            let replacement =
                hex::decode(hex).map_err(|error| format!("invalid replacement hex: {error}"))?;
            if replacement.len() != CHUNK_BYTES {
                return Err(format!(
                    "replacement chunk has {} bytes, expected {CHUNK_BYTES}",
                    replacement.len()
                ));
            }
            let range = chunk_range(*index, bytes.len())?;
            bytes[range].copy_from_slice(&replacement);
        }
        ProofMutation::RemoveChunk { index } => {
            let range = chunk_range(*index, bytes.len())?;
            bytes.drain(range);
        }
        ProofMutation::IncrementScalar { index } => {
            let range = chunk_range(*index, bytes.len())?;
            let repr: [u8; 32] = bytes[range.clone()].try_into().unwrap();
            let scalar = Option::<pallas::Base>::from(pallas::Base::from_repr(repr))
                .ok_or_else(|| format!("chunk {index} is not a canonical scalar"))?;
            let incremented = scalar + pallas::Base::ONE;
            bytes[range].copy_from_slice(incremented.to_repr().as_ref());
        }
        ProofMutation::FlipPointSign { index } => {
            let range = chunk_range(*index, bytes.len())?;
            bytes[range.end - 1] ^= 0x80;
        }
    }
    Ok(bytes)
}

fn make_case(
    id: &str,
    generated: &GeneratedProof,
    inputs_id: &str,
    rust_instances: &[Instance],
    mutation: ProofMutation,
    covers: &[&str],
    vk: &VerifyingKey,
) -> Result<CaseSnapshot, String> {
    let bytes = mutation_bytes(&generated.proof, &mutation)?;
    let outcome = verify_outcome(&Proof::new(bytes), vk, rust_instances);
    Ok(CaseSnapshot {
        id: id.to_owned(),
        proof: generated.proof.id.clone(),
        inputs: inputs_id.to_owned(),
        mutation,
        rust_outcome: outcome,
        covers: covers.iter().map(|cover| (*cover).to_owned()).collect(),
    })
}

fn build_snapshot() -> Result<Snapshot, String> {
    verify_pinned_submodules()?;
    if !(cfg!(target_arch = "x86_64") && cfg!(target_os = "linux") && cfg!(target_env = "gnu")) {
        return Err(format!(
            "fixtures pin Rust target {PINNED_RUST_TARGET}; this binary was built for {}/{}/{}",
            env::consts::ARCH,
            env::consts::OS,
            if cfg!(target_env = "gnu") {
                "gnu"
            } else if cfg!(target_env = "musl") {
                "musl"
            } else {
                "other"
            }
        ));
    }
    if usize::BITS != 64 {
        return Err(format!(
            "fixtures pin Rust usize to 64 bits, but this target has {} bits",
            usize::BITS
        ));
    }

    let circuit_version = OrchardCircuitVersion::PostNu6_3;
    let pk = ProvingKey::build(circuit_version);
    let vk = VerifyingKey::build(circuit_version);

    let restricted_one = generate_proof(0x53, 1, false, "restricted_one", &pk, &vk)?;
    let unrestricted_one = generate_proof(0x55, 1, true, "unrestricted_one", &pk, &vk)?;
    let restricted_two = generate_proof(0x4d, 2, false, "restricted_two", &pk, &vk)?;
    let (wrong_inputs, wrong_rust_instances) =
        generate_inputs_only(0xac, 1, false, "restricted_one_wrong_inputs")?;
    let (spends_disabled_inputs, spends_disabled_rust_instances) = generate_inputs_only_with_flags(
        0xad,
        1,
        BundleVersion::ironwood_v3(),
        Flags::SPENDS_DISABLED,
        "unrestricted_one_spends_disabled_inputs",
    )?;
    let (outputs_disabled_inputs, outputs_disabled_rust_instances) =
        generate_inputs_only_with_flags(
            0xae,
            1,
            BundleVersion::ironwood_v3(),
            Flags::OUTPUTS_DISABLED,
            "unrestricted_one_outputs_disabled_inputs",
        )?;
    let (wrong_two_inputs, wrong_two_rust_instances) =
        generate_inputs_only(0xaf, 2, false, "restricted_two_wrong_inputs")?;
    let empty_inputs = InputSnapshot {
        id: "empty_inputs".to_owned(),
        instances_le_hex: vec![],
    };

    let mut cases = vec![
        make_case(
            "valid_restricted_one",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::Identity,
            &["verified", "restricted_flag", "one_action"],
            &vk,
        )?,
        make_case(
            "valid_unrestricted_one",
            &unrestricted_one,
            &unrestricted_one.input.id,
            &unrestricted_one.rust_instances,
            ProofMutation::Identity,
            &["verified", "unrestricted_flag", "one_action"],
            &vk,
        )?,
        make_case(
            "valid_restricted_two",
            &restricted_two,
            &restricted_two.input.id,
            &restricted_two.rust_instances,
            ProofMutation::Identity,
            &["verified", "restricted_flag", "two_actions"],
            &vk,
        )?,
        make_case(
            "trailing_bytes_are_ignored",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::Append {
                hex: "a55a".to_owned(),
            },
            &["trailing_bytes"],
            &vk,
        )?,
        make_case(
            "wrong_public_input",
            &restricted_one,
            &wrong_inputs.id,
            &wrong_rust_instances,
            ProofMutation::Identity,
            &["constraint_system_failure", "instance_binding"],
            &vk,
        )?,
        make_case(
            "spends_disabled_public_input",
            &unrestricted_one,
            &spends_disabled_inputs.id,
            &spends_disabled_rust_instances,
            ProofMutation::Identity,
            &["constraint_system_failure", "spends_disabled_flag"],
            &vk,
        )?,
        make_case(
            "outputs_disabled_public_input",
            &unrestricted_one,
            &outputs_disabled_inputs.id,
            &outputs_disabled_rust_instances,
            ProofMutation::Identity,
            &["constraint_system_failure", "outputs_disabled_flag"],
            &vk,
        )?,
        make_case(
            "wrong_two_action_public_input",
            &restricted_two,
            &wrong_two_inputs.id,
            &wrong_two_rust_instances,
            ProofMutation::Identity,
            &["constraint_system_failure", "two_action_rejection"],
            &vk,
        )?,
        make_case(
            "zero_proofs_for_nonempty_stream",
            &restricted_one,
            &empty_inputs.id,
            &[],
            ProofMutation::Identity,
            &["zero_proofs"],
            &vk,
        )?,
        make_case(
            "canonical_advice_eval_tamper",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::IncrementScalar { index: 32 },
            &["constraint_system_failure", "canonical_scalar_tamper"],
            &vk,
        )?,
        make_case(
            "noncanonical_scalar",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::ReplaceChunk {
                index: 32,
                hex: "ff".repeat(CHUNK_BYTES),
            },
            &["transcript_scalar_decode"],
            &vk,
        )?,
        make_case(
            "noncanonical_point",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::ReplaceChunk {
                index: 0,
                hex: "ff".repeat(CHUNK_BYTES),
            },
            &["transcript_point_decode"],
            &vk,
        )?,
        make_case(
            "identity_point",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::ReplaceChunk {
                index: 0,
                hex: "00".repeat(CHUNK_BYTES),
            },
            &["transcript_identity_rejection"],
            &vk,
        )?,
        make_case(
            "omitted_permutation_eval",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::RemoveChunk { index: 104 },
            &["permutation_eval_desync"],
            &vk,
        )?,
        make_case(
            "truncated_final_multiopen_u",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::Truncate {
                len: 130 * CHUNK_BYTES,
            },
            &["opening", "multiopen_u"],
            &vk,
        )?,
        make_case(
            "corrupted_ipa_round",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::FlipPointSign { index: 132 },
            &["constraint_system_failure", "ipa_round"],
            &vk,
        )?,
        make_case(
            "corrupted_ipa_c",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::IncrementScalar { index: 154 },
            &["constraint_system_failure", "ipa_final"],
            &vk,
        )?,
        make_case(
            "corrupted_ipa_f",
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::IncrementScalar { index: 155 },
            &["constraint_system_failure", "ipa_final"],
            &vk,
        )?,
    ];

    // Every transition between Rust proof-reading blocks is represented. Half-chunk truncation at
    // the first point additionally covers `read_exact` on a partial encoding.
    let truncations = [
        ("empty", 0),
        ("partial_first_point", 16),
        ("after_advice_commitments", 10 * CHUNK_BYTES),
        ("after_lookup_permuted", 16 * CHUNK_BYTES),
        ("after_permutation_products", 19 * CHUNK_BYTES),
        ("after_lookup_products", 22 * CHUNK_BYTES),
        ("after_random_commitment", 23 * CHUNK_BYTES),
        ("after_quotient_pieces", 31 * CHUNK_BYTES),
        ("after_instance_evals", 32 * CHUNK_BYTES),
        ("after_advice_evals", 57 * CHUNK_BYTES),
        ("after_fixed_evals", 86 * CHUNK_BYTES),
        ("after_random_eval", 87 * CHUNK_BYTES),
        ("after_permutation_common", 102 * CHUNK_BYTES),
        ("inside_permutation_sets", 105 * CHUNK_BYTES),
        ("after_permutation_sets", 110 * CHUNK_BYTES),
        ("after_lookup_evals", 125 * CHUNK_BYTES),
        ("after_q_prime", 126 * CHUNK_BYTES),
        ("after_multiopen_u", 131 * CHUNK_BYTES),
        ("after_s_commitment", 132 * CHUNK_BYTES),
        ("inside_ipa_rounds", 143 * CHUNK_BYTES),
        ("before_ipa_c", 154 * CHUNK_BYTES),
        ("before_ipa_f", 155 * CHUNK_BYTES),
    ];
    for (name, len) in truncations {
        cases.push(make_case(
            &format!("truncated_{name}"),
            &restricted_one,
            &restricted_one.input.id,
            &restricted_one.rust_instances,
            ProofMutation::Truncate { len },
            &["truncated_stream", name],
            &vk,
        )?);
    }

    if cases.len() != EXPECTED_CASES {
        return Err(format!(
            "fixture producer built {} cases, expected exactly {EXPECTED_CASES}",
            cases.len()
        ));
    }

    let mut coverage = BTreeMap::<String, Vec<String>>::new();
    for case in &cases {
        for branch in &case.covers {
            coverage
                .entry(branch.clone())
                .or_default()
                .push(case.id.clone());
        }
    }
    let required_coverage = REQUIRED_COVERAGE.iter().copied().collect::<BTreeSet<_>>();
    if required_coverage.len() != REQUIRED_COVERAGE.len() {
        return Err("required coverage inventory contains duplicate IDs".to_owned());
    }
    if required_coverage.len() != EXPECTED_COVERAGE_IDS {
        return Err(format!(
            "required coverage inventory has {} IDs, expected exactly {EXPECTED_COVERAGE_IDS}",
            required_coverage.len()
        ));
    }

    let actual_coverage = coverage.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let missing = required_coverage
        .difference(&actual_coverage)
        .copied()
        .collect::<Vec<_>>();
    let extra = actual_coverage
        .difference(&required_coverage)
        .copied()
        .collect::<Vec<_>>();
    if !missing.is_empty() || !extra.is_empty() {
        return Err(format!(
            "coverage IDs differ from the exact inventory: missing=[{}], extra=[{}]",
            missing.join(", "),
            extra.join(", ")
        ));
    }

    Ok(Snapshot {
        schema_version: SCHEMA_VERSION,
        source: SourcePins {
            orchard: ORCHARD_PIN.to_owned(),
            halo2: HALO2_PIN.to_owned(),
            rocq_of_rust: ROCQ_OF_RUST_PIN.to_owned(),
            rust_target: PINNED_RUST_TARGET.to_owned(),
            usize_bits: usize::BITS,
        },
        shape: Shape {
            circuit: "PostNu6_3".to_owned(),
            k: 11,
            instance_width: 10,
            proof_base_bytes: 2720,
            proof_bytes_per_action: 2272,
            advice_queries: 25,
            fixed_queries: 29,
            permutation_columns: 15,
            permutation_sets: 3,
            lookups: 3,
            quotient_pieces: 8,
            multiopen_point_sets: 5,
            ipa_rounds: 11,
        },
        proofs: vec![
            restricted_one.proof,
            unrestricted_one.proof,
            restricted_two.proof,
        ],
        inputs: vec![
            restricted_one.input,
            unrestricted_one.input,
            restricted_two.input,
            wrong_inputs,
            spends_disabled_inputs,
            outputs_disabled_inputs,
            wrong_two_inputs,
            empty_inputs,
        ],
        cases,
        branch_coverage: coverage
            .into_iter()
            .map(|(id, cases)| CoverageEntry { id, cases })
            .collect(),
    })
}

fn render(snapshot: &Snapshot) -> Result<String, String> {
    serde_json::to_string_pretty(snapshot)
        .map(|mut json| {
            json.push('\n');
            json
        })
        .map_err(|error| format!("could not encode snapshot JSON: {error}"))
}

fn check_or_write(path: &Path, check: bool) -> Result<(), String> {
    let generated = render(&build_snapshot()?)?;
    if check {
        let checked_in = fs::read_to_string(path)
            .map_err(|error| format!("could not read {}: {error}", path.display()))?;
        if generated != checked_in {
            return Err(format!(
                "{} is stale; regenerate it with this tool",
                path.display()
            ));
        }
    } else {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("could not create {}: {error}", parent.display()))?;
        }
        fs::write(path, generated)
            .map_err(|error| format!("could not write {}: {error}", path.display()))?;
    }
    Ok(())
}

fn usage(program: &str) -> String {
    format!("usage: {program} [--check] [--output PATH]")
}

fn main() {
    let mut args = env::args();
    let program = args.next().unwrap_or_else(|| "fixture-runner".to_owned());
    let mut check = false;
    let mut output = PathBuf::from("Garden/Orchard/Verifier/Snapshots/post_nu6_3.json");
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--check" => check = true,
            "--output" => {
                output = args.next().map(PathBuf::from).unwrap_or_else(|| {
                    eprintln!("{}", usage(&program));
                    std::process::exit(2);
                });
            }
            "--help" | "-h" => {
                println!("{}", usage(&program));
                return;
            }
            _ => {
                eprintln!("unknown argument: {arg}\n{}", usage(&program));
                std::process::exit(2);
            }
        }
    }

    if let Err(error) = check_or_write(&output, check) {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
