# Garden

> A friendly framework to formally verify zero-knowledge systems

<p align="center">
  <img src="garden.svg" alt="logo" width="256" />
</p>

## Service

To ensure your ZK circuits are correct, down to the implementation level, please contact us at [&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;](mailto:&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;)!

We provide formal verification services as well as training and custom developments. Our cost is **$50 per line of circuit code** (excluding comments) to formally verify the absence of under-constrains and functional correctness.

The verification that we deliver can be integrated into your CI system and maintained on your side. Formal verification is the highest quality of security audit that you can get. The Ethereum Foundation, through its project [Verified zkEVM](https://verified-zkevm.org/), considers it mandatory for large-scale ZK systems.

## What

Zero-knowledge applications are one of the most anticipated innovations in the blockchain space. They allow the scaling of transactions almost indefinitely and preserve the privacy of user information.

One issue is that these systems are very complex. Testing alone cannot ensure the security of these systems, and billions worth of assets will be at risk.

Formal verification, based on a mathematical analysis of the code, is the solution to ensure the safety of such systems.

With [Garden](https://github.com/formal-land/garden), we are building a friendly, open-source, [Rocq](https://rocq-prover.org/) framework to formally verify zero-knowledge systems.

## Support

We are first targeting the two following circuit formats:

- [Circom](https://github.com/iden3/circom)
- Mina-like Rust circuits like in [keccak/interpreter.rs](https://github.com/o1-labs/proof-systems/blob/master/o1vm/src/interpreters/keccak/interpreter.rs)

## Training

To make safe cryptography available to everyone, we will be hosting training sessions on this website: [https://cryptography.academy/](https://cryptography.academy/)

## Related

Here are some related projects:

- [cLean](https://github.com/Verified-zkEVM/clean) ZK-circuits (Lean)
- [ZKLib](https://github.com/Verified-zkEVM/ZKLib) crypto-graphic primitives (Lean)

You can make a pull request to add yours!
