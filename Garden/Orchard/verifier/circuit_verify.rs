//! Snapshot of orchard/src/circuit.rs verifying-key, instance encoding, and
//! Proof::verify (formal-land/orchard @ 05d899241b7a907d9c47dc5d3d7b3aa1361d785c).
//! Review/traceability only; not part of the Rocq build.

/// The verifying key for the Orchard Action circuit.
///
/// Build with [`VerifyingKey::build`] for an explicit circuit version.
#[derive(Debug)]
pub struct VerifyingKey {
    pub(crate) params: halo2_proofs::poly::commitment::Params<vesta::Affine>,
    pub(crate) vk: plonk::VerifyingKey<vesta::Affine>,
    circuit_version: OrchardCircuitVersion,
}

impl VerifyingKey {
    /// Builds the verifying key for the given circuit version.
    ///
    /// See [`OrchardCircuitVersion`] for which version to use.
    pub fn build(circuit_version: OrchardCircuitVersion) -> Self {
        let params = halo2_proofs::poly::commitment::Params::new(K);
        let circuit = Circuit::empty(circuit_version);

        let vk = plonk::keygen_vk(&params, &circuit).unwrap();

        VerifyingKey {
            params,
            vk,
            circuit_version,
        }
    }

    /// The circuit version this verifying key was built for.
    pub fn circuit_version(&self) -> OrchardCircuitVersion {
        self.circuit_version
    }

    /// Returns whether this verifying key supports the cross-address restriction.
    pub fn supports_cross_address_restriction(&self) -> bool {
        self.circuit_version.supports_cross_address_restriction()
    }
}

/// The proving key for the Orchard Action circuit.
///
/// Build with [`ProvingKey::build`] for an explicit circuit version.
/// The resulting proofs verify only under a compatible [`VerifyingKey`].
#[derive(Debug)]
pub struct ProvingKey {
    params: halo2_proofs::poly::commitment::Params<vesta::Affine>,
    pk: plonk::ProvingKey<vesta::Affine>,
    circuit_version: OrchardCircuitVersion,
}

impl ProvingKey {
    /// Builds the proving key for the given circuit version.
    ///
    /// See [`OrchardCircuitVersion`] for which version to use.
    pub fn build(circuit_version: OrchardCircuitVersion) -> Self {
        let params = halo2_proofs::poly::commitment::Params::new(K);
        let circuit = Circuit::empty(circuit_version);

        let vk = plonk::keygen_vk(&params, &circuit).unwrap();
        let pk = plonk::keygen_pk(&params, vk, &circuit).unwrap();

        ProvingKey {
            params,
            pk,
            circuit_version,
        }
    }

    /// The circuit version this proving key produces proofs for.
    pub fn circuit_version(&self) -> OrchardCircuitVersion {
        self.circuit_version
    }

    /// Returns whether this proving key supports the cross-address restriction.
    pub fn supports_cross_address_restriction(&self) -> bool {
        self.circuit_version.supports_cross_address_restriction()
    }
}

/// Public inputs to the Orchard Action circuit.
///
/// # Invariants
///
/// Every `Instance` has a non-identity `rk`.
#[derive(Clone, Debug)]
pub struct Instance {
    anchor: Anchor,
    cv_net: ValueCommitment,
    nf_old: Nullifier,
    rk: VerificationKey<SpendAuth>,
    cmx: ExtractedNoteCommitment,
    enable_spend: bool,
    enable_output: bool,
    cross_address_disabled: bool,
}

impl Instance {
    /// Constructs an [`Instance`] from its constituent parts.
    ///
    /// This API can be used in combination with [`Proof::verify`] to build verification
    /// pipelines for many proofs, where you don't want to pass around the full bundle.
    /// Use [`Bundle::verify_proof`] instead if you have the full bundle.
    ///
    /// The provided [`Flags`] are encoded into the spend/output enable public inputs and
    /// the `disableCrossAddress` public input, which is set to the negation of
    /// [`Flags::cross_address_enabled`]. If cross-address transfers are disabled,
    /// callers must use a proving or verifying key whose circuit version supports the
    /// cross-address restriction; [`Proof::create`], [`Proof::verify`], and
    /// [`crate::bundle::BatchValidator`] enforce this.
    ///
    /// Returns `None` if `rk` is the identity [`pasta_curves::pallas::Point`].
    /// zcashd v6.12.1 and Zebra 4.3.1 both added a consensus rule rejecting
    /// transactions whose Orchard actions have an identity `rk`; the Zcash
    /// protocol specification will be updated to match, and this crate
    /// aligns with that rule.
    ///
    /// See:
    /// - <https://zodl.com/zcashd-zebra-april-2026-disclosure/>
    /// - <https://zfnd.org/zebra-4-3-1-critical-security-fixes-dockerized-mining-and-ci-hardening/>
    ///
    /// [`Bundle::verify_proof`]: crate::Bundle::verify_proof
    pub fn from_parts(
        anchor: Anchor,
        cv_net: ValueCommitment,
        nf_old: Nullifier,
        rk: VerificationKey<SpendAuth>,
        cmx: ExtractedNoteCommitment,
        flags: Flags,
    ) -> Option<Self> {
        (!rk.is_identity()).then_some(Instance {
            anchor,
            cv_net,
            nf_old,
            rk,
            cmx,
            enable_spend: flags.spends_enabled(),
            enable_output: flags.outputs_enabled(),
            cross_address_disabled: !flags.cross_address_enabled(),
        })
    }

    /// Returns the Merkle tree anchor of this instance.
    pub(crate) fn anchor(&self) -> &Anchor {
        &self.anchor
    }

    /// Returns the commitment to the net value of this instance.
    pub(crate) fn cv_net(&self) -> &ValueCommitment {
        &self.cv_net
    }

    /// Returns the nullifier of the note being spent by this instance.
    pub(crate) fn nf_old(&self) -> &Nullifier {
        &self.nf_old
    }

    /// Returns the randomized verification key of this instance.
    pub(crate) fn rk(&self) -> &VerificationKey<SpendAuth> {
        &self.rk
    }

    /// Returns the commitment to the new note being created by this instance.
    pub(crate) fn cmx(&self) -> &ExtractedNoteCommitment {
        &self.cmx
    }

    /// Returns whether the spend is enabled for this instance.
    pub(crate) fn enable_spend(&self) -> bool {
        self.enable_spend
    }

    /// Returns whether the output is enabled for this instance.
    pub(crate) fn enable_output(&self) -> bool {
        self.enable_output
    }

    /// Returns whether cross-address transfers are disabled for this instance.
    pub(crate) fn cross_address_disabled(&self) -> bool {
        self.cross_address_disabled
    }

    fn to_halo2_instance(&self) -> [[vesta::Scalar; 10]; 1] {
        let mut instance = [vesta::Scalar::zero(); 10];

        instance[ANCHOR] = self.anchor.inner();
        instance[CV_NET_X] = self.cv_net.x();
        instance[CV_NET_Y] = self.cv_net.y();
        instance[NF_OLD] = self.nf_old.inner();

        let rk = pallas::Point::from_bytes(&self.rk.clone().into())
            .expect("the cached byte encoding of a VerificationKey<_> is canonical")
            .to_affine()
            .coordinates()
            .expect("rk is non-identity by construction");

        instance[RK_X] = *rk.x();
        instance[RK_Y] = *rk.y();
        instance[CMX] = self.cmx.inner();
        instance[ENABLE_SPEND] = vesta::Scalar::from(u64::from(self.enable_spend));
        instance[ENABLE_OUTPUT] = vesta::Scalar::from(u64::from(self.enable_output));
        // Instance columns are zero-padded over the evaluation domain, so for statements
        // where this flag is false, this encoding is commitment-identical to the historical
        // nine-row encoding. Pre-NU 6.3 circuits leave this row unconstrained, which is why
        // restricted statements must never reach those keys (see `Proof::create` and
        // `Proof::verify`).
        instance[DISABLE_CROSS_ADDRESS] =
            vesta::Scalar::from(u64::from(self.cross_address_disabled));

        [instance]
    }
}

impl Proof {
    /// Creates a proof for the given circuits and instances.
    ///
    /// The resulting proof verifies only under a compatible [`VerifyingKey`] (see
    /// [`OrchardCircuitVersion`]).
    ///
    /// Returns [`plonk::Error::Synthesis`] if any circuit's version does not match `pk`'s
    /// version, since `pk` could not produce a valid proof for it.
    ///
    /// Returns [`plonk::Error::InvalidInstances`] if any instance has
    /// `disableCrossAddress = 1` and `pk` is not an
    /// [`OrchardCircuitVersion::PostNu6_3`] proving key.
    ///
    /// All instances of a bundle carry the same `disableCrossAddress` value; that uniformity
    /// is the bundle layer's invariant, and is not checked here.
    pub fn create(
        pk: &ProvingKey,
        circuits: &[Circuit],
        instances: &[Instance],
        mut rng: impl RngCore,
    ) -> Result<Self, plonk::Error> {
        if circuits
            .iter()
            .any(|c| c.circuit_version != pk.circuit_version)
        {
            return Err(plonk::Error::Synthesis);
        }
        if instances.iter().any(Instance::cross_address_disabled)
            && !pk.supports_cross_address_restriction()
        {
            return Err(plonk::Error::InvalidInstances);
        }

        let instances: Vec<_> = instances.iter().map(|i| i.to_halo2_instance()).collect();
        let instances: Vec<Vec<_>> = instances
            .iter()
            .map(|i| i.iter().map(|c| &c[..]).collect())
            .collect();
        let instances: Vec<_> = instances.iter().map(|i| &i[..]).collect();

        let mut transcript = Blake2bWrite::<_, vesta::Affine, _>::init(vec![]);
        plonk::create_proof(
            &pk.params,
            &pk.pk,
            circuits,
            &instances,
            &mut rng,
            &mut transcript,
        )?;
        Ok(Proof(transcript.finalize()))
    }

    /// Verifies this proof with the given instances.
    ///
    /// # Errors
    ///
    /// Returns [`plonk::Error::InvalidInstances`] if any instance has
    /// `disableCrossAddress = 1` and `vk` is not an
    /// [`OrchardCircuitVersion::PostNu6_3`] verifying key.
    ///
    /// Also returns an error if proof verification fails.
    pub fn verify(&self, vk: &VerifyingKey, instances: &[Instance]) -> Result<(), plonk::Error> {
        if instances.iter().any(Instance::cross_address_disabled)
            && !vk.supports_cross_address_restriction()
        {
            return Err(plonk::Error::InvalidInstances);
        }

        let instances: Vec<_> = instances.iter().map(|i| i.to_halo2_instance()).collect();
        let instances: Vec<Vec<_>> = instances
            .iter()
            .map(|i| i.iter().map(|c| &c[..]).collect())
            .collect();
        let instances: Vec<_> = instances.iter().map(|i| &i[..]).collect();

        let strategy = SingleVerifier::new(&vk.params);
        let mut transcript = Blake2bRead::init(&self.0[..]);
        plonk::verify_proof(&vk.params, &vk.vk, strategy, &instances, &mut transcript)
    }

    /// Adds this proof to the given batch for verification with the given instances.
    ///
    /// Internal to [`BatchValidator`], which is the only public batch path. A raw batch
    /// does not know which [`VerifyingKey`] it will be finalized with, so it cannot enforce
    /// that instances disabling cross-address transfers are only finalized with a key whose
    /// circuit version constrains the `disableCrossAddress` public input (see
    /// [`OrchardCircuitVersion::supports_cross_address_restriction`]). [`BatchValidator`]
    /// binds its key at construction and rejects such bundles in [`add_bundle`] before they
    /// reach this method; exposing this directly would let a caller sidestep that check by
    /// finalizing the batch against an unsupported key.
    ///
    /// [`BatchValidator`]: crate::bundle::BatchValidator
    /// [`add_bundle`]: crate::bundle::BatchValidator::add_bundle
    pub(crate) fn add_to_batch(
        &self,
        batch: &mut BatchVerifier<vesta::Affine>,
        instances: Vec<Instance>,
    ) {
        let instances = instances
            .iter()
            .map(|i| {
                i.to_halo2_instance()
                    .into_iter()
                    .map(|c| c.into_iter().collect())
                    .collect()
            })
            .collect();

        batch.add_proof(instances, self.0.clone());
    }
}

