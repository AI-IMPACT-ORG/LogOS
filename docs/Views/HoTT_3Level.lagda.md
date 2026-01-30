<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% View — HoTT-Style Positioning (S/H/G + Reflection)

```agda
{-# OPTIONS --safe #-}
module docs.Views.HoTT_3Level where

-- Typechecked “view surface” for the 3-level HoTT-style reading (S/H/G).
--
-- Keep this module lightweight to avoid name clashes when imported alongside
-- other views/tests.

open import LogOS.Prelude public
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
import LogOS.Theorems.Meta.CHL.ViewTheorems as ViewTheorems

module Quotes {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module V = ViewTheorems.For K
  open V.HoTT3Level public

  private
    coh-SH-exists : _
    coh-SH-exists = coh-SH

    coh-H∂-exists : _
    coh-H∂-exists = coh-H∂

    decode-Box-exists : _
    decode-Box-exists = decode-Box

    guarded-fixed-exists : _
    guarded-fixed-exists = guarded-fixed

    stable-truth-exists : _
    stable-truth-exists = stable-truth

    projection-exists : _
    projection-exists = V.Projections.projection
```

Purpose
-------
This view positions LogOS using “HoTT-style” language: a stratified system with
explicit coherences between levels, and explicit choices about when (and
whether) mutual refinement (≈) is upgraded to propositional equality (≡).

Interpretation (analogy):
where this note mentions physics/complexity as motivation, treat that as interpretation only.
The authoritative claims are exactly the typechecked theorem surfaces cited below.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

Notation (local)
----------------
- `c ⊑ d`: refinement/entailment in a preorder.
- `c ≈ d`: mutual refinement.
- `P ↔ Q`: satisfaction equivalence.
- `x ≡ y`: propositional equality (`_≡_`), not judgmental equality.
When this note says “coherence”, it refers to `_↔_`-statements unless the text explicitly says `≡`.

Scope (formal)
--------------
- Parameter: `Kernel Sig Q`.
- Surface: `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `HoTT3Level`).

Dictionary (literature ↔ LogOS)
-------------------------------

| Literature concept | LogOS identifier(s) | Notes |
|---|---|---|
| “Levels” / strata of meaning | S/H/G tiers (`Sat_S`, `Sat_H w c`, `Flow` + `Th*`) | These are explicit interfaces, not universe levels. |
| Equivalence-first coherence | `_↔_` (`LogOS/Syntax/Prop.agda`) | Used for tier coherences instead of judgmental equality. |
| Modality / local operator | `Flow` (guarded closure) | Inflationary + idempotent-lax; pre-fixed points (hence fixed up to `≈`) are “stable truths”. |
| Truncation/extensionality upgrades | antisymmetry / proof-irrelevance packs | Upgrades mutual refinement to equality when assumed. |
| Reflection (syntax-in-logic) | `Code`, `encode`, `decode`, `Guard`, `Body` | A reflective interface, not an additional truth layer. |
| Resource/budget algebra | `QAdapter` (`LogOS/Minimal/Adapter.agda`) | Unital quantale in the finite-join sense (not complete); used for graded/budgeted variants. |

Core definitions (literature style)
-----------------------------------

**Definition (Tier coherences).** A kernel provides explicit bridges:
- S→H: `Sat_S w φ ↔ Sat_H w (TransH φ)` (coherence `coh-LH`), and
- H→boundary indexing: `Sat_H w c ↔ Sat_H_bnd (to∂ w) c` (coherence `sat-coh`).

**Definition (Stability).** A boundary constraint \(t\) is stable when
\(\mathrm{Flow}(t) ⊑ t\) (pre-fixed point). Because `Flow` is inflationary,
stability implies “fixed up to mutual refinement”.

**Definition (Reflection coherence).** The guard step on code decodes to the
guarded step on constraints (`guard-decode`), grounding “compute-then-stabilise”
as a literal kernel law rather than a meta-level convention.

Assumptions (explicit)
----------------------
- This repo does **not** assume univalence/HITs/univalent universes globally; any extensionality is local and explicit.
- Equality-level “HoTT laws” typically require **proof-irrelevance** (for refinement proofs) and/or **antisymmetry** (for constraint preorders).

What is novel here (residual vs the literature)
-----------------------------------------------
- Matches literature: “transport-first” coherence (`↔` / bi-implications) and stratified semantics.
- Weaker/lax by default: no global HoTT axiom set (no univalence/HITs assumed); refinement and closure live at preorder strength.
- Added by ports/adapters: tier coherences are explicit interfaces, and stability is a named closure modality (`Flow`, `Th*`) rather than a meta-level convention.
- Assumption-scoped: equality-level upgrades (proof-irrelevance/antisymmetry) and μ/limit facts (ωCPO/finite-first/continuity bundles) are explicit hypotheses.

Theorem spine (authoritative)
-----------------------------
- `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `HoTT3Level`):
  `coh-SH`, `coh-H∂`, `decode-Box`, `guarded-fixed`, `stable-truth`.
- Projection certificate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Projections`),
  `projection`.
- The prose below is explanatory; the statements above are the authoritative claims.

Micro-example (two different equalities, used deliberately)
-----------------------------------------------------------
- Tier coherences are stated as `↔` (satisfaction equivalence), so they remain valid
  under port/adaptor transport.
- Reflection coherence is stated as `≡` (propositional equality of decoded constraints),
  because it is a literal kernel law about decoding.

Pointers (no repetition)
------------------------
- Kernel field map and tier glossary: `docs/LogOS_Core_Spec.lagda.md`.
- μ/limit reasoning and hypotheses: `docs/Terminology.lagda.md` and `docs/Kernel/ClaimRegister.lagda.md`.
- Institution-style presentation: `docs/Views/MultiInstitution.lagda.md`.

Extended discussion (optional)
-----------------------------
Everything below elaborates on the reading above. The authoritative claims are the
typechecked surfaces cited in the theorem spine.

Key points:

- LogOS is built as a **three-tier** system (S/H/G) with **explicit coherences**
  between the tiers.
- The core does **not** assume `_≡_` coincides with `_↔_` or with mutual refinement (`≈`);
  it uses preorders and explicit bi-implications. This is the host-minimal, transport-friendly default.
- “Univalence-like” principles appear as **opt-in upgrades** (e.g. antisymmetry / faithfulness),
  allowing movement between an extensional (set-like) and a homotopical (`_↔_`-first) reading
  without changing the kernel.

Three levels in the implementation
----------------------------------
LogOS names the tiers:

1) **S — Strict**
   - A formula carrier `Fml` and a satisfaction predicate `Sat_S`.
   - Entailment is *derived* from `Sat_S` as `StrictTruth.EntailsS`
     (`LogOS/Minimal/Truth.agda`).

2) **H — Homotypical** (LogOS term: world-/context-indexed boundary semantics)
   - A satisfaction predicate `Sat_H w c` for boundary constraints.
   - An invariance/projector `Inv_H` (inflationary, idempotent‑lax). If you additionally assume
     monotonicity for `Inv_H`, it upgrades to a closure/nucleus operator; LogOS keeps that
     strength explicit (bundle: `HomotypicalTruth.InvarianceMono` in `LogOS/Minimal/Truth.agda`).
   - This tier is designed so theorems are phrased in terms of *structure* and *transport*
     rather than judgmental equalities.

3) **G — Guarded**
   - A closure operator on boundary constraints (a nucleus/projector). In the Kernel code this
     step is named `Flow` (the `Flow` field of `Truth.GuardedCore.GuardedClosure` in `LogOS/Minimal/Truth.agda`).
     Unlike `Inv_H`, `Flow` already includes monotonicity in its interface.
   - A distinguished lax fixed-point witness `Th*` (interpretation: “global stable truth”). With optional antisymmetry
     (and, for μ/limit results, `OmegaCPO` + `FiniteFirst`), one can relate `Th*` to the Kleene
     least pre-fixed point `μ Flow`. Antisymmetry only upgrades “leastness up to refinement” to
     equality-level leastness.
   - Interpretation (analogy): this tier is the “stability/communication” layer: local truths become globally stable via
     the closure step.

4) **R — Reflection (Code)**
   - A code layer (`Code`, `encode`, `decode`, `Guard`, `Body`) internalising admissible steps.
   - This is the “+” in “3+ levels”: it is not another truth predicate, but a reflective interface
     that lets the kernel speak about its own boundary reasoning at `decode` level.
   - The reflection/guard coherence law is a kernel field (unguarded kernel: `LogOS/Kernel.agda`,
     uniform interface: `LogOS/Kernel/LogicKernel.agda`).
   - Optional tightening (functorial syntax): a signature-indexed “sentence/program” layer with
     covariant translation along `SigHom` lives in `LogOS/Free/ConstraintsOverSig.agda`. This is
     the institution-style `Sen` direction and complements the kernel’s contravariant model
     reindexing (`reindexKernel`). If you want strict-formula translation at the kernel surface,
     use `reindexKernelWithFml`.

The coherence laws between tiers are **fields of the Kernel record** (`LogOS/Kernel.agda`):

- `coh-LH` connects strict S-truth to H-truth via `TransH : Fml → Con_bnd` using a *bi-implication*
  (`_↔_`), not a judgmental equality.
- `sat-coh` connects world-indexed H-truth to boundary-indexed H-truth via `to∂`.

```agda
-- Anchor: the kernel coherence `sat-coh` is phrased using the signature’s `to∂`.
open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Kernel using (Kernel)
open import LogOS.Syntax.Prop using (_↔_)
import LogOS.Minimal.Truth as Truth

private
  module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) where
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    sat-coh-typed
      : ∀ (w : LogOSSignature.Cosp Sig)
          (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K)))
      → _↔_
          (HT.HLayer.Sat_H (Kernel.HTruth K) w c)
          (Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c)
    sat-coh-typed = Kernel.sat-coh K
```

Why this is “HoTT-style” (and not just “3 modules”)
---------------------------------------------------
Two design choices are key:

### 1) Equivalences are first-class (and equality is not forced)
Across the repo, “coherence” is phrased as `_↔_` (pairs of functions) and order inequalities,
not judgmental equalities. This mirrors the HoTT discipline:

- identify structure via `_↔_` (bi-implication) and transport,
- treat equality (judgmental or propositional) as *additional structure*, not the default.

In code, this appears as:
- preorders as the default notion of “constraint order” (`LogOS/Minimal/Con.agda`),
- coherence records using `_↔_` from `LogOS/Syntax/Prop.agda`.

### 2) Modal/closure structure is explicit (Flow as a modality)
The guarded tier packages a closure/nucleus `Flow`. The stable fragment can be
presented as pre‑fixed points (`Flow t ⊑ t`); because `Flow` is inflationary, this
is the same as mutual refinement (`t ≈ Flow t`) without assuming
antisymmetry.

Fixed points of a nucleus are the
standard categorical semantics of a modality (monotone, inflationary, idempotent‑lax endomap),
and under antisymmetry this upgrades to equality-level idempotence; LogOS makes this explicit
at the boundary logic level.

This is what powers:
- “local truth vs global truth” theorems (stable truth transport),
- diagonal/Rice/Tarski meta-theorems phrased at decode level,
- physics/complexity “resource bottleneck” interfaces phrased as closure-stability claims.

Where “univalence” fits (what exists today)
-------------------------------------------
LogOS already contains the **slots** where univalence-like upgrades live:

### Poset extensionality (analogy: 0-truncated univalence)
The core is preorder-based. As an analogy: if you assume antisymmetry, then “mutual entailment” becomes equality.
This is the poset analogue of univalence at truncation level 0:

> if `c ⊑ d` and `d ⊑ c`, then `c ≡ d`.

In the library this is the optional “upgrade from preorder to partial order”
provided by `PartialOrder` in `LogOS/Minimal/Con.agda`.

### Faithfulness of embeddings (univalence-like reflection principle)
In operator/bridge packs (e.g. Hilbert–Pólya), a common “univalence-like” assumption is that an
embedding reflects equality (no information loss). This is packaged explicitly as a record
field (e.g. `EmbedFaithful` in the HP interface).

These are not global axioms; they are **local packs** you choose to assume when you want a
fully extensional reading.

What is *not* claimed by default
------------------------------------
This 1.0 library does *not* claim “full HoTT” in the sense of:

- a built-in univalence axiom for all types,
- higher inductive types,
- a univalent universe hierarchy.

Instead, the repo is engineered so that:

1) the core stays small and host-minimal,
2) `_↔_`-first coherence is the default (via `_↔_`, projectors, and transport),
3) univalence-like principles can be added as *explicit, scoped* assumption packs
   where the application warrants it (e.g. collapsing mutual-refinement classes under antisymmetry/proof-irrelevance).

How to use this in writing
--------------------------
If you want a precise, publication-friendly sentence:

> LogOS is a three-tier logic (S/H/G) whose coherences are expressed by satisfaction equivalences (↔) and closure
> operators; univalence-like extensionality principles are optional, explicitly packaged upgrades
> (antisymmetry/faithfulness), rather than hidden global axioms.

Cross references
----------------
- Views index: `docs/Views/All.lagda.md`
- Kernel definition and coherence fields: `LogOS/Kernel.agda`
- Minimal tier interfaces: `LogOS/Minimal/Truth.agda`
- Preorders/partial orders: `LogOS/Minimal/Con.agda`
- `_↔_` and negation discipline: `LogOS/Syntax/Prop.agda`
- CHL capstone: `docs/Views/CurryHowardLambek.lagda.md`
