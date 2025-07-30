# LLZK

In this folder we put our formalization of the [LLZK](https://github.com/Veridise/llzk-lib) language in Rocq, together with generated example files of translation from `.llzk` files with their specifications and proofs.

The files in this folder are:

- [`M.v`](M.v): The monad defining the LLZK language.
- [`mastermind.v`](mastermind.v): The generated translation of the `mastermind.llzk` example (not working yet).
- [`translated.v`](translated.v): The generated translation of the example we are considering to develop the LLZK formalization (working!)
- [`verification.v`](verification.v): The specification and formal verification of all the definitions in the `translated.v` file.
