# Crosslink2 TLA⁺ Specification

A TLA⁺ specification of the Crosslink2 protocol and its subprotocols, modeled as a state machine.

📖 [Read the full TFL book](https://electric-coin-company.github.io/tfl-book/)

## Disclamer

This specification is currently a proof of concept. It is not a complete or final specification of the Crosslink2 protocol. It is a work in progress and may change over time.

Feedback and improvements are very welcome!

## Motivation

The goal is to create a simple yet expressive model of the Crosslink2 protocol that allows us to reason about properties such as safety and liveness. The model should be easy to understand, modify, and extend while still capturing some of the protocol’s inherent complexity.

## The protocol

We model the Crosslink2 protocol and its subprotocols as a state machine with the following components:

- `bc_chains`, `bft_chains`, and `crosslink2_chains` are sequences of chains. At any execution time `t` and for each node `i`, we have a local chain for that node. For example, `bft_chains[i]` represents the BFT chain of node `i` at current time `t`. Chains are updated as the protocol executes.

- Initialization: At `t = 0`, each chain for each node starts with the genesis block of its protocol. For example: `bft_chains[i] = <<bft_genesis_block>>`.

- State transitions (`t > 0`): One or more of the following may occur:

  - An honest BC-node updates its `bc_chain` to the best chain and appends a `bc-block`.

  - An honest BFT-node updates its `bft_chain` to the best chain and appends a `bft-block`.

  - A byzantine BFT-node may update its `bft_chain` to a valid chain and append a faulty `bft-block`.

  - An honest Crosslink-node updates its view to a new finalized `fin` chain.

  - The state remains unchanged.

The TLA⁺ specification is defined in [crosslink2.tla](crosslink2.tla).
A generated PDF version is available at [crosslink2.pdf](crosslink2.pdf).

## Contributing

Feedback, bug reports, and pull requests are welcome!  

## License

This project is released under the **MIT License**. See [LICENSE](LICENSE) for details.
