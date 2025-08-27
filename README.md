# Garden

> A friendly framework to formally verify zero-knowledge circuits 🍀

![Garden picture](docs/garden.jpeg)

## What

It is a common consensus that, in order to be ready for the Ethereum L1, zkVMs must be formally verified. This includes verifying the circuit constraints, which are one of the most critical parts of a zkVM. With **Garden**, we provide a friendly framework in the [Rocq](https://rocq-prover.org/) formal system to make sure that the three main properties of a circuit hold:

- **Determinism**: only one possible trace for each input;
- **Functional correctness**: the circuit computes the right output (typically the RISC-V semantics);
- **Completeness**: the circuit never blocks.

You can get more details about the properties to verify in our blog post [🦄 What to verify in a zkVM](https://formal.land/blog/2025/08/12/verification-of-zkvm). The list of zkVMs with their formal verification status is maintained on [Ethproofs.org](https://ethproofs.org/).

The Garden framework aims to be:

- **Effective**: the formal verification of circuits must be efficient, as this is a competitive space;
- **Maintainable**: no black magic;
- **Tied to the code**: the formal model must be tied to the code generating the circuits, not the low-level constraints themselves.

We provide several examples (many of which are Work in Progress at the moment) about:

- The verification of pre-compiles (Blake3, Keccak, and Sha256);
- The verification of an OpenVM chip (BranchEq)

We handle circuits at the implementation level in:

- [Plonky3](https://github.com/Plonky3/Plonky3)
- [LLZK](https://github.com/Veridise/llzk-lib)
- [Circom](https://github.com/iden3/circom)

## Install

You can look at the build instructions in the [BUILD.md](docs/BUILD.md) file.

## Contact

For more information or to discuss security, please get in touch with us at [&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;](mailto:&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;)!

## Related

Here are some related projects:

- [cLean](https://github.com/Verified-zkEVM/clean) ZK-circuits (Lean)
- [ZKLib](https://github.com/Verified-zkEVM/ZKLib) crypto-graphic primitives (Lean)

You can make a pull request to add your project if we are missing something!

<p align="center">
  <img src="garden.svg" alt="logo" width="256" />
</p>
