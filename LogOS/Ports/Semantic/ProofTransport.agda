{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.ProofTransport where

-- “Logic system I/O” via proof systems:
--
-- Given a semantics-preserving translation between presentations, we can
-- *pull back* existing provers/checkers (their inputs and proof outputs) along
-- that translation. This makes interoperability usable with real downstream
-- logic tools: once you have one prover/checker for a presentation, you get one
-- for every other presentation (and, via `SatMor`, across changing logics).

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop
open import LogOS.Syntax.ProofSystem

open import LogOS.Ports.Semantic.InterlinguaCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)

import LogOS.Ports.Semantic.InterlinguaCore as InterlinguaCore
import LogOS.Ports.Semantic.HeteroInterlinguaCore as HeteroCore

-- ---------------------------------------------------------------------------
-- Shared-satisfaction case (classic interlingua).
-- ---------------------------------------------------------------------------

module Shared
  {ℓCtx ℓCon ℓSat : Level}
  {Ctx : Set ℓCtx}
  {Con : Set ℓCon}
  {SatC : Ctx → Con → Set ℓSat}
  {ℓForm₁ ℓForm₂ : Level}
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx Con SatC)
  where

  private
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂
    module C  = InterlinguaCore.ForPresentations P₁ P₂

    Form₁ = P1.Form
    Form₂ = P2.Form

  -- Global validity (a common “output predicate” for proof systems).
  Valid₁ : Form₁ → Set (ℓCtx ⊔ ℓSat)
  Valid₁ φ = ∀ p → P1.SatF p φ

  Valid₂ : Form₂ → Set (ℓCtx ⊔ ℓSat)
  Valid₂ ψ = ∀ p → P2.SatF p ψ

  -- Pull back a prover for presentation 2 along the forced translation.
  pullbackProver
    : ∀ {ℓW}
    → ProofSystem {ℓI = ℓForm₂} {ℓP = ℓCtx ⊔ ℓSat} {ℓW = ℓW} Form₂ Valid₂
    → ProofSystem {ℓI = ℓForm₁} {ℓP = ℓCtx ⊔ ℓSat} {ℓW = ℓW} Form₁ Valid₁
  pullbackProver PS₂ =
    record
      { Proof    = λ φ → Proof PS₂ (C.translate φ)
      ; Check    = λ φ pr → Check PS₂ (C.translate φ) pr
      ; decCheck = λ φ pr → decCheck PS₂ (C.translate φ) pr
      ; sound    = λ φ pr ok p →
          let
            v₂ : Valid₂ (C.translate φ)
            v₂ = sound PS₂ (C.translate φ) pr ok
          in
          Prop.from (C.translate-preserves-Sat p φ) (v₂ p)
      }

  -- Pull back a model-checker: certifies satisfaction for a specific context.
  --
  -- This matches typical external “solver output” workflows (certificate + checker).
  pullbackModelChecker
    : ∀ {ℓW}
    → ProofSystem {ℓI = ℓCtx ⊔ ℓForm₂} {ℓP = ℓSat} {ℓW = ℓW}
        (Ctx × Form₂)
        (λ where (p , ψ) → P2.SatF p ψ)
    → ProofSystem {ℓI = ℓCtx ⊔ ℓForm₁} {ℓP = ℓSat} {ℓW = ℓW}
        (Ctx × Form₁)
        (λ where (p , φ) → P1.SatF p φ)
  pullbackModelChecker PS₂ =
    record
      { Proof    = λ x →
          let (p , φ) = x in
          Proof PS₂ (p , C.translate φ)
      ; Check    = λ x pr →
          let (p , φ) = x in
          Check PS₂ (p , C.translate φ) pr
      ; decCheck = λ x pr →
          let (p , φ) = x in
          decCheck PS₂ (p , C.translate φ) pr
      ; sound    = λ x pr ok →
          let
            (p , φ) = x
            sat₂ : P2.SatF p (C.translate φ)
            sat₂ = sound PS₂ (p , C.translate φ) pr ok
          in
          Prop.from (C.translate-preserves-Sat p φ) sat₂
      }

-- ---------------------------------------------------------------------------
-- Heterogeneous case: along a satisfaction morphism `SatMor`.
-- ---------------------------------------------------------------------------

module AlongSatMor
  {ℓCtx₁ ℓCon₁ ℓSat₁ : Level}
  {Ctx₁ : Set ℓCtx₁}
  {Con₁ : Set ℓCon₁}
  {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
  {ℓCtx₂ ℓCon₂ ℓSat₂ : Level}
  {Ctx₂ : Set ℓCtx₂}
  {Con₂ : Set ℓCon₂}
  {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
  (m  : SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
  {ℓForm₁ ℓForm₂ : Level}
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ Con₂ Sat₂)
  where

  private
    module M  = SatMor m
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂
    module H  = HeteroCore.For m P₁ P₂

    Form₁ = P1.Form
    Form₂ = P2.Form

    ℓV₁ = ℓCtx₁ ⊔ ℓSat₁
    ℓV₂ = ℓCtx₂ ⊔ ℓSat₂
    ℓV' = ℓV₁ ⊔ ℓSat₂

  -- Validity in the source presentation.
  Valid₁ : Form₁ → Set ℓV₁
  Valid₁ φ = ∀ p → P1.SatF p φ

  -- Validity in the target presentation (pulled back along `mapCtx`).
  Valid₂↑ : Form₂ → Set (ℓCtx₁ ⊔ ℓSat₂)
  Valid₂↑ ψ = ∀ p → P2.SatF (M.mapCtx p) ψ

  -- Global validity in the target presentation (over all target contexts).
  --
  -- If your “prover” is already phrased as global validity over `Ctx₂` (the
  -- common case when `Ctx` is a model class), you can always restrict it to
  -- `Valid₂↑` by precomposing with `mapCtx`.
  Valid₂ : Form₂ → Set ℓV₂
  Valid₂ ψ = ∀ p → P2.SatF p ψ

  restrictValid₂ : ∀ ψ → Valid₂ ψ → Valid₂↑ ψ
  restrictValid₂ ψ v₂ p = v₂ (M.mapCtx p)

  -- Pull back a prover for the target presentation along the heterogeneous translation.
  --
  -- NOTE: this expects a prover for `Valid₂↑`, i.e. validity only over contexts
  -- of the form `mapCtx p`. If you have a prover for global validity `Valid₂`
  -- (the common case), use `pullbackProverFromGlobal` below.
  --
  -- Because `ProofSystem` ties the checker level to the proposition level, we
  -- lift both the checker and the proposition into a common universe level.
  pullbackProver
    : ∀ {ℓW}
    → ProofSystem {ℓI = ℓForm₂} {ℓP = ℓCtx₁ ⊔ ℓSat₂} {ℓW = ℓW} Form₂ Valid₂↑
    → ProofSystem {ℓI = ℓForm₁} {ℓP = ℓV'} {ℓW = ℓW}
        Form₁ (λ φ → Lift ℓSat₂ (Valid₁ φ))
  pullbackProver PS₂ =
    record
      { Proof    = λ φ → Proof PS₂ (H.translate φ)
      ; Check    = λ φ pr → Lift ℓSat₁ (Check PS₂ (H.translate φ) pr)
      ; decCheck = decCheck'
      ; sound    = λ φ pr ok →
          let
            v₂ : Valid₂↑ (H.translate φ)
            v₂ = sound PS₂ (H.translate φ) pr (Lift.lower ok)

            v₁ : Valid₁ φ
            v₁ p = Prop.from (H.translate-preserves-Sat p φ) (v₂ p)
          in
          lift v₁
      }
    where
      decCheck'
        : ∀ φ pr
        → Lift ℓSat₁ (Check PS₂ (H.translate φ) pr)
            ⊎
          ¬ Lift ℓSat₁ (Check PS₂ (H.translate φ) pr)
      decCheck' φ pr with decCheck PS₂ (H.translate φ) pr
      ... | inj₁ ok = inj₁ (lift ok)
      ... | inj₂ notOk = inj₂ (λ ok' → notOk (Lift.lower ok'))

  -- Alias with an explicit name to avoid misreading `pullbackProver` as global.
  pullbackProverOnImage = pullbackProver

  -- Common specialization: start from a target prover for *global* validity (`Valid₂`).
  --
  -- This is the standard “pull back proofs/certificates along translation” move:
  -- prove `translate φ` globally in the target system, then restrict to `mapCtx p`
  -- and rewrite back to the source satisfaction.
  pullbackProverFromGlobal
    : ∀ {ℓW}
    → ProofSystem {ℓI = ℓForm₂} {ℓP = ℓV₂} {ℓW = ℓW} Form₂ Valid₂
    → ProofSystem {ℓI = ℓForm₁} {ℓP = ℓV₁ ⊔ ℓV₂} {ℓW = ℓW}
        Form₁ (λ φ → Lift ℓV₂ (Valid₁ φ))
  pullbackProverFromGlobal PS₂ =
    record
      { Proof    = λ φ → Proof PS₂ (H.translate φ)
      ; Check    = λ φ pr → Lift ℓV₁ (Check PS₂ (H.translate φ) pr)
      ; decCheck = decCheck'
      ; sound    = λ φ pr ok →
          let
            v₂ : Valid₂ (H.translate φ)
            v₂ = sound PS₂ (H.translate φ) pr (Lift.lower ok)

            v₁ : Valid₁ φ
            v₁ p = Prop.from (H.translate-preserves-Sat p φ) (v₂ (M.mapCtx p))
          in
          lift v₁
      }
    where
      decCheck'
        : ∀ φ pr
        → Lift ℓV₁ (Check PS₂ (H.translate φ) pr)
            ⊎
          ¬ Lift ℓV₁ (Check PS₂ (H.translate φ) pr)
      decCheck' φ pr with decCheck PS₂ (H.translate φ) pr
      ... | inj₁ ok    = inj₁ (lift ok)
      ... | inj₂ notOk = inj₂ (λ ok → notOk (Lift.lower ok))

  -- Context-specific checker (pulled back along `mapCtx` + translation).
  pullbackModelChecker
    : ∀ {ℓW}
    → ProofSystem {ℓI = ℓCtx₁ ⊔ ℓForm₂} {ℓP = ℓSat₂} {ℓW = ℓW}
        (Ctx₁ × Form₂)
        (λ where (p , ψ) → P2.SatF (M.mapCtx p) ψ)
    → ProofSystem {ℓI = ℓCtx₁ ⊔ ℓForm₁} {ℓP = ℓSat₁ ⊔ ℓSat₂} {ℓW = ℓW}
        (Ctx₁ × Form₁)
        (λ where (p , φ) → Lift ℓSat₂ (P1.SatF p φ))
  pullbackModelChecker PS₂ =
    record
      { Proof    = λ x →
          let (p , φ) = x in
          Proof PS₂ (p , H.translate φ)
      ; Check    = λ x pr →
          let (p , φ) = x in
          Lift ℓSat₁ (Check PS₂ (p , H.translate φ) pr)
      ; decCheck = decCheck'
      ; sound    = λ x pr ok →
          let
            (p , φ) = x
            sat₂ : P2.SatF (M.mapCtx p) (H.translate φ)
            sat₂ = sound PS₂ (p , H.translate φ) pr (Lift.lower ok)
          in
          lift (Prop.from (H.translate-preserves-Sat p φ) sat₂)
      }
    where
      decCheck'
        : ∀ x pr
        → Lift ℓSat₁ (Check PS₂ (x .fst , H.translate (x .snd)) pr)
            ⊎
          ¬ Lift ℓSat₁ (Check PS₂ (x .fst , H.translate (x .snd)) pr)
      decCheck' x pr with decCheck PS₂ (x .fst , H.translate (x .snd)) pr
      ... | inj₁ ok = inj₁ (lift ok)
      ... | inj₂ notOk = inj₂ (λ ok' → notOk (Lift.lower ok'))

  -- Common specialization: start from a target model-checker phrased over `Ctx₂`.
  --
  -- This is the standard “pull back certificates along translation” move, plus
  -- a context map (`mapCtx`) and a satisfaction rewrite.
  pullbackModelCheckerFromGlobal
    : ∀ {ℓW}
    → ProofSystem {ℓI = ℓCtx₂ ⊔ ℓForm₂} {ℓP = ℓSat₂} {ℓW = ℓW}
        (Ctx₂ × Form₂)
        (λ where (p , ψ) → P2.SatF p ψ)
    → ProofSystem {ℓI = ℓCtx₁ ⊔ ℓForm₁} {ℓP = ℓSat₁ ⊔ ℓV₂} {ℓW = ℓW}
        (Ctx₁ × Form₁)
        (λ where (p , φ) → Lift ℓV₂ (P1.SatF p φ))
  pullbackModelCheckerFromGlobal PS₂ =
    record
      { Proof    = λ x →
          Proof PS₂ (M.mapCtx (x .fst) , H.translate (x .snd))
      ; Check    = λ x pr →
          Lift (ℓSat₁ ⊔ ℓCtx₂) (Check PS₂ (M.mapCtx (x .fst) , H.translate (x .snd)) pr)
      ; decCheck = decCheck'
      ; sound    = λ x pr ok →
          let
            sat₂ : P2.SatF (M.mapCtx (x .fst)) (H.translate (x .snd))
            sat₂ = sound PS₂ (M.mapCtx (x .fst) , H.translate (x .snd)) pr (Lift.lower ok)

            sat₁ : P1.SatF (x .fst) (x .snd)
            sat₁ = Prop.from (H.translate-preserves-Sat (x .fst) (x .snd)) sat₂
          in
          lift sat₁
      }
    where
      decCheck'
        : ∀ x pr
        → Lift (ℓSat₁ ⊔ ℓCtx₂) (Check PS₂ (M.mapCtx (x .fst) , H.translate (x .snd)) pr)
            ⊎
          ¬ Lift (ℓSat₁ ⊔ ℓCtx₂) (Check PS₂ (M.mapCtx (x .fst) , H.translate (x .snd)) pr)
      decCheck' x pr with decCheck PS₂ (M.mapCtx (x .fst) , H.translate (x .snd)) pr
      ... | inj₁ ok    = inj₁ (lift ok)
      ... | inj₂ notOk = inj₂ (λ ok → notOk (Lift.lower ok))
