<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Meta Theorems — Pattern and Usage
=================================

This folder contains small, explicit interfaces and transport utilities to derive
Rice/Tarski/Gödel/Löb‑style theorems inside the logic from clear, local assumptions.

The core idea
- Work primarily at the boundary (decode) level. Kernel exposes safe reflection:
  - `reify` with `reify-decode`: decode (reify γ) ≡ decode γ
  - `Body∂` with `body-decode`: decode (Body γ) ≡ Body∂ (decode γ)
- State minimal side‑conditions as small records (no global postulates):
  - `DecodeExtensional K P`: P depends only on `decode`
  - `Provability K`: schematic provability pack (extensionality, nontriviality)
- Prove on the canonical (initial) model once; transport via the canonical fold to any kernel.
  - The transport lemma itself is textbook: decidability pulls back along a reduction.
  - Any diagonalisation/fixed‑point assumptions live in the *local* FreeKernel proof, not in transport.

Entry points
- Assumptions (structural): `LogOS/Theorems/Meta/Assumptions/Core.agda`
- Assumptions (diagonalisation): `LogOS/Theorems/Meta/Assumptions/Diagonal.agda`
  - Umbrella re-export: `LogOS/Theorems/Meta/Assumptions.agda`
- Transport: `LogOS/Theorems/Meta/Full.agda`
- Rice/Tarski (conditional wrappers): `LogOS/Theorems/Meta/Rice.agda`, `LogOS/Theorems/Meta/Tarski.agda`
- Löb/Gödel (conditional): `LogOS/Theorems/Meta/Lob.agda`, `LogOS/Theorems/Meta/Godel.agda` (kernel-independent core lemma: `LogOS/Theorems/Meta/LobCore.agda`)
- No omniscience / event horizon packaging (diagonal-against-decidable-observers form): `LogOS/Theorems/Meta/NoOmniscience.agda`
- Spectral separation partial output (assumption-only, anti-totality): `LogOS/Theorems/Meta/SpectralSeparationOutput.agda`
- Math/Physics observer+opacity bundle (graded-kernel friendly): `LogOS/Theorems/Meta/MathPhysSynthesis.agda`
- Maximal communicable truth (Flow-stable): `LogOS/Theorems/Meta/CommunicableTruth.agda`
- Regulated truth → observable truth (MathTruth pack): `LogOS/Theorems/Meta/MathTruth.agda`
- Limit publicisation laws (reflector property, cofinality, naturality): `LogOS/Theorems/Meta/LimitPublicisation.agda`
- Minimal dagger/* infrastructure (quadratic positivity shims): `LogOS/Theorems/Meta/Dagger.agda`

Typical usage (Rice/Tarski shape)
1) Choose a kernel `K` and a property `P : Code K → Set`.
2) Prove `¬ DeciderC` for the pullback of `P` along the canonical fold on `FreeKernel`.
3) Use `noDecider-transport` to derive `¬ DeciderC` for `P` on any kernel via fold.

Typical usage (Gödel/Löb shape)
1) Package `Provability K` (decode‑extensional predicate with nontriviality; add HBLClassic/diagonalization assumptions if desired).
2) Provide the standard provability‑side assumptions as explicit packs:
   - Preferred: `InternalHomWitness` + `DecodeImp⊑` (or `QuoteSubst` + `DecodeImp`) to *derive* `Diagonalization`, then `HBLClassic` + `ImpRules` (use `Meta/Lob.loebAxiom-from-InternalHom` / `Meta/Lob.loebAxiom-from-QuoteSubst`).
   - Corollary: if you already have `Diagonalization`, combine it with `HBLClassic` + `ImpRules` via `Meta/Lob.loebFromHBL`.
3) Use the Gödel packaging (`LogOS/Theorems/Meta/Godel.agda`) to derive the incompleteness claim for your model.

Notes
- The metatheorems are conditional: they require explicit assumption packs (e.g., extensionality,
  nontriviality, diagonalisation/fixed‑point principles, HBLClassic/Löb) and in some cases a local proof at the
  canonical FreeKernel; transport to any kernel is automated.
- `LogOS/Theorems/Meta/Full.agda` also exports the general lemma `noDecider-by-pullback`:
  undecidability pushes forward along any `KernelHom` by contrapositive pullback of deciders.
- Some optional packs (e.g. `LogOS/Theorems/Meta/Diagonal.agda`) phrase diagonalization using
  code-level equalities; these are still explicit assumptions and are not required by the
  transport wrappers.
- For Gödel 2, provide `Provability`, `ProvabilityOps`, and a `LoebAxiom` (either given directly, or obtained via `Meta/Lob.loebAxiom-from-InternalHom` / `Meta/Lob.loebAxiom-from-QuoteSubst`, or via the corollary `Meta/Lob.loebFromHBL` when `Diagonalization` is already packaged); use `Meta/Godel.incompleteness`.
- Model‑specific instantiations (e.g., concrete fixed points) should live outside the core library and depend only on these small, explicit assumption records.
