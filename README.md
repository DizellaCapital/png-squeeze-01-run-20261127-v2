# PNG squeeze v2

[![make.fun](https://img.shields.io/badge/make.fun-bounty-blue)](https://make.fun/c/png-squeeze-01-run-20261127)
[![Node](https://img.shields.io/badge/node-22-green)](https://nodejs.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Lossless PNG encoder for the [make.fun png-squeeze-01-run-20261127 bounty](https://make.fun/c/png-squeeze-01-run-20261127) ($100, top 50).

## Approach

- **Colour-type reduction** per image: palette (≤256 colours, luminance-sorted, with tRNS when needed), grey, grey+alpha, RGB, or RGBA — whichever the pixels require.
- **Scanline filter selection**: tries fixed-0, fixed-Paeth, per-row min-sum and per-row log-cost filters; picks the winner by actual zlib size (level-6 proxy).
- **Optimal-parsing DEFLATE**: hash-chain longest-match search (sublen array: smallest distance per match length), shortest-path DP over literal/match tokens with iterative Huffman cost refinement, per-block dynamic Huffman (fixed-Huffman fallback), canonical codes, RLE code-length header. Match candidates are cached across DP iterations. Chain depth adapts to colour depth (deeper for palette/grey, where the best matches hide deep in the chain).
- Fully deterministic: fixed amount of work per instance, no clock reads, no network, Node stdlib only.

## Files

- `main.ts` — the whole encoder (decode → reduce → filter → deflate → encode).
