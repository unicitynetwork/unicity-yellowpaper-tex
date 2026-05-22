# Unicity Yellowpaper

Low-level specification for the Unicity protocol. The Yellowpaper is the
best entry point for engineering details that are intentionally brief in
the higher-level papers, including consensus-layer operation, data
availability, and how aggregation shards operate as clusters of machines.

## Download

- Latest PDF:
  [unicity-yellowpaper.pdf](https://github.com/unicitynetwork/unicity-yellowpaper-tex/releases/download/latest/unicity-yellowpaper.pdf)
- Source repository:
  [github.com/unicitynetwork/unicity-yellowpaper-tex](https://github.com/unicitynetwork/unicity-yellowpaper-tex/)

## Unicity Paper Map

- [Unicity Whitepaper](https://github.com/unicitynetwork/whitepaper)
  ([PDF](https://github.com/unicitynetwork/whitepaper/releases/download/latest/Unicity.pdf)) -
  protocol overview, tokenomics, and network architecture.
- [Unicity Yellowpaper](https://github.com/unicitynetwork/unicity-yellowpaper-tex)
  ([PDF](https://github.com/unicitynetwork/unicity-yellowpaper-tex/releases/download/latest/unicity-yellowpaper.pdf)) -
  low-level protocol specification, including consensus-layer engineering
  details, data availability, and aggregation shard operation.
- [Unicity Infrastructure: the Aggregation Layer / Unicity Bluepaper](https://github.com/unicitynetwork/aggr-layer-paper)
  ([PDF](https://github.com/unicitynetwork/aggr-layer-paper/releases/download/latest/aggregation-layer.pdf)) -
  aggregation-layer design, sharded SMT commitments, inclusion and
  non-inclusion proofs, and the ZK consistency proof model.
- [Unicity Execution Layer](https://github.com/unicitynetwork/execution-model-tex)
  ([PDF](https://github.com/unicitynetwork/execution-model-tex/releases/download/latest/unicity-execution-layer.pdf)) -
  off-chain transaction execution, service-side privacy, user-wallet
  privacy, and formal security proofs.
- [Unicity: Predicates and Atomic Swaps](https://github.com/unicitynetwork/unicity-predicates-tex)
  ([PDF](https://github.com/unicitynetwork/unicity-predicates-tex/releases/download/latest/unicity-predicates.pdf)) -
  programmable spending conditions ("smart contracts") with a use-case, trustless atomic swaps.


## Building locally:

1. install a complete tex environment

    `brew install mactex-no-gui`  (macOS, using homebrew)

    `apt-get install texlive-full` (debian and derivatives)

2. Build using three passes of `pdflatex` or use the provided Makefile.


## Building locally (using docker):

- Pull the image:

    `docker pull registry.gitlab.com/islandoftex/images/texlive:latest` (might need to put `sudo` in front)

- Build the paper (from the project root): note that `pdflatex` has to be executed 3 times (to resolve all cross-references)

    `docker run -i --rm --name latex -v "$PWD":/usr/src/app -w /usr/src/app/ registry.gitlab.com/islandoftex/images/texlive:latest pdflatex unicity-yellowpaper.tex`
