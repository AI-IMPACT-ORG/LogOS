<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Metamath artifact format (`.mmdb`)

This document specifies the **explicit handover artifact** used by the Metamath
pipeline:

The canonical optional tooling entrypoint for this pipeline is
[`tools/metamath/README.md`](../../tools/metamath/README.md). The
`scripts/metamath/**` files are wrappers around that tooling, not a second
public tooling surface.

- A (fast) **adapter** parses and proof-checks a Metamath database (`set.mm`),
  then writes a versioned binary artifact `db.mmdb` + a `manifest.json`.
- A second adapter can **export** this artifact into **safe Agda modules**
  implementing `LogOS.Ports.Metamath.Database`.

The artifact boundary is deliberate: it makes the trust boundary and the
transformer stack explicit.

## Semantic roundtrip contract

The artifact format is only one layer of the Metamath story. The bidirectional
Agda surface has a weaker, refinement-shaped contract:

- `Formula -> PFormula -> Formula` is certified only up to the
  environment-threaded renaming computed by the reifier/decoder pair.
- `Formula -> token row -> Formula` is exact only after the same two
  interpretation steps used by the parser pipeline:
  - close the conclusion under the mandatory frame's implicit outer `∀`;
  - normalize away vacuous binders introduced by that closure.
- Emission is intentionally partial. Unsupported host fragments currently
  include terms that do not project into the Set.MM surface (for example
  `pairT`), and parsing back into `Formula` still rejects metavariable-bearing
  `PFormula`.

The user-facing semantic note for this boundary lives in
[`docs/Interpretations/Applications/Metamath_Roundtrip.lagda.md`](../../docs/Interpretations/Applications/Metamath_Roundtrip.lagda.md).

## Pipeline usage (Haskell `mmc`, recommended)

This repo contains a small, repo-local compiler/exporter:

- sources: `tools/metamath/mmc/**`
- build script: `scripts/metamath/mmc_build.sh` (writes `_build/metamath/mmc/mmc`)

All Agda invocations should go through `scripts/metamath/agda.sh`, which injects:

- `--no-libraries`
- `-W all -W error`

Build `mmc`:

```bash
bash scripts/metamath/mmc_build.sh
```

Compile `set.mm` to an artifact:

```bash
mkdir -p _build/metamath
# place set.mm at: _build/metamath/set.mm

_build/metamath/mmc/mmc compile _build/metamath/set.mm \
  --out _build/metamath/setmm_art \
  --check-proofs \
  --progress-every 5000
```

Export a small safe Agda `Database` module for a prefix:

```bash
_build/metamath/mmc/mmc export-agda _build/metamath/setmm_art \
  --max-assertions 200 \
  --emit-agda _build/metamath/Metamath/SetMM_200.agda \
  --agda-module Metamath.SetMM_200

bash scripts/metamath/agda.sh --safe \
  _build/metamath/Metamath/SetMM_200.agda
```

## Reference parser/emitter (Python, small DBs)

The reference parser lives under the same canonical tooling subtree:

- `tools/metamath/parse_mm/**`

For a readable, repo-local reference implementation, use:

```bash
python3 -B tools/metamath/parse_mm/parse_mm.py _build/metamath/set.mm \
  --out _build/metamath/set.mm.json
```

## File layout (v1)

All integers are **little-endian**.

### Header (32 bytes)

Offset | Size | Meaning
---|---:|---
0  | 4  | magic bytes `MMDB`
4  | 4  | `version` (u32) = `1`
8  | 4  | `flags` (u32)
12 | 8  | `offsetSymbols` (u64) absolute byte offset of the Symbols section
20 | 4  | `numSymbols` (u32)
24 | 4  | `numAssertions` (u32)
28 | 4  | reserved (u32) = `0`

Flags:

- bit 0: `proofsChecked` (1 iff all `$p` proofs were checked during compilation)

### Assertions section (starts at offset 32)

Repeated `numAssertions` times:

Field | Type | Meaning
---|---|---
`labelLen` | u32 | number of bytes in the Metamath label
`label` | bytes | label bytes (ASCII/UTF-8 as-is)
`numHyps` | u32 | number of hypotheses (premises)
`hyps` | ... | repeated `numHyps` times
`concl` | ... | conclusion formula

Each hypothesis formula:

Field | Type | Meaning
---|---|---
`len` | u32 | number of symbols
`syms` | u32[] | `len` symbol indices

The conclusion formula uses the same `(len, syms)` encoding.

Notes:

- Hypotheses stored here are the **mandatory frame** for each `$a/$p` assertion:
  mandatory `$f` hypotheses are expanded into their two-symbol formulas
  `[typecode, var]`, and mandatory `$e` hypotheses are stored verbatim.
- Proof token streams are **not** stored in the artifact.

### Symbols section (starts at `offsetSymbols`)

Field | Type | Meaning
---|---|---
`numSymbols` | u32 | must match the header
`symbols` | ... | repeated `numSymbols` times

Each symbol entry:

Field | Type | Meaning
---|---|---
`len` | u32 | number of bytes
`bytes` | bytes | symbol token bytes (ASCII/UTF-8 as-is)

Symbol indices in formulas are 0-based, corresponding to this table order.
