{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.ProofSearchGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude.Product using (Σ; _,_; _×_; fst; snd; proj₁; proj₂)
open import LogOS.Prelude.NatOrder using (dec≤ℕ)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Computation.Decider as Dec using (dec×)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.LanguageWitnessW as LWW
import LogOS.Domain.Complexity.PhysicsClassesWGraded as PCW
import LogOS.Domain.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
import LogOS.Domain.Complexity.PhysProofBridgeWGraded as PBW
import LogOS.Syntax.ProofSystem as PSCore

-- Grade-native proof search target (Route B):
-- same structure as the ℕ version, but costs live in the grade.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  module C = PCW.For {ℓI = ℓI} {ℓW = ℓ} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound
  module B = PBW.For {ℓI = ℓI} {ℓW = ℓ} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  Language = C.Language

  record ProofSystem (P : Input → Set ℓ) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      core : PSCore.ProofSystem {ℓW = ℓ} Input P

      psize     : ∀ {x} → PSCore.ProofSystem.Proof core x → ℕ
      polyBound : ℕ → ℕ

      checkCost  : ∀ x → PSCore.ProofSystem.Proof core x → QAdapter.Scale Q
      checkBound : ℕ → ℕ
      polyCheck  : PolyPred.isPoly Pℕ checkBound
      checkCost≤ : ∀ x p → QAdapter._≤s_ Q (checkCost x p) (gradeBound (checkBound (size x)))
      wsize≤checkCost : ∀ x p → QAdapter._≤s_ Q (gradeBound (psize p)) (checkCost x p)

    open PSCore.ProofSystem core public

  Thm : ∀ {P} → ProofSystem P → Language
  Thm {P} PS x =
    Σ (ProofSystem.Proof PS x)
      (λ p → (LWW._≤ℕ_ (ProofSystem.psize PS p) (ProofSystem.polyBound PS (size x)))
           × ProofSystem.Check PS x p)

  CheckThm : ∀ {P} (PS : ProofSystem P) → (x : Input) → ProofSystem.Proof PS x → Set ℓ
  CheckThm PS x p =
    (LWW._≤ℕ_ (ProofSystem.psize PS p) (ProofSystem.polyBound PS (size x)))
    × ProofSystem.Check PS x p

  decCheckThm
    : ∀ {P} (PS : ProofSystem P)
      → ∀ x p → CheckThm PS x p ⊎ ¬ CheckThm PS x p
  decCheckThm PS x p =
    Dec.dec×
      (dec≤ℕ (ProofSystem.psize PS p) (ProofSystem.polyBound PS (size x)))
      (ProofSystem.decCheck PS x p)

  witnessSystemForThm
    : ∀ {P} (PS : ProofSystem P) → LWW.WitnessSystemW Input (Thm PS)
  witnessSystemForThm PS =
    record
      { W        = ProofSystem.Proof PS
      ; wsize    = ProofSystem.psize PS
      ; size     = size
      ; polyBound = ProofSystem.polyBound PS
      ; Check    = CheckThm PS
      ; decCheck = decCheckThm PS
      ; sound    = λ x p pr → p , pr
      ; complete = λ x thm →
          let p  = proj₁ thm in
          let le = fst (proj₂ thm) in
          let ok = snd (proj₂ thm) in
          p , (le , (le , ok))
      }

  physWitnessForThm : ∀ {P} (PS : ProofSystem P) → C.PhysWitnessW (Thm PS)
  physWitnessForThm PS =
    record
      { WS        = witnessSystemForThm PS
      ; checkCost  = ProofSystem.checkCost PS
      ; checkBound = ProofSystem.checkBound PS
      ; polyCheck  = ProofSystem.polyCheck PS
      ; checkCost≤ = ProofSystem.checkCost≤ PS
      }

  thm-inPhysNPw
    : ∀ {P} (PS : ProofSystem P) → C.PhysNPw (Thm PS)
  thm-inPhysNPw PS = physWitnessForThm PS , tt

  thm-separates
    : ∀ {P} (PS : ProofSystem P)
      → (MM : B.MergeMeasure (Thm PS))
      → B.ProofLowerBound (Thm PS) MM
      → C.PhysNPw (Thm PS) × ¬ C.PhysP (Thm PS)
  thm-separates PS MM PLB =
    thm-inPhysNPw PS
    , C.notPhysP (B.superPolyCostFromProof MM PLB)

  thm-inPhysNPwG
    : ∀ {P} (PS : ProofSystem P) → C.PhysNPwG (Thm PS)
  thm-inPhysNPwG PS = C.toPhysWitnessWG (physWitnessForThm PS) , tt

  thm-separatesG
    : ∀ {P} (PS : ProofSystem P)
      → C.PhysSeparationWG (Thm PS)
      → C.PhysNPwG (Thm PS) × ¬ C.PhysPG (Thm PS)
  thm-separatesG PS sep =
    C.PhysSeparationWG.inNPwG sep ,
    C.notPhysPG (C.PhysSeparationWG.detSuperPolyG sep)

  -- Cost-guard witness system: ensure verification cost dominates witness size.
  module CS = PCWCG.For {ℓI = ℓI} {ℓW = ℓ} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound

  thm-inPhysNPwCostGuards
    : ∀ {P} (PS : ProofSystem P) → CS.PhysNPwCostGuards (Thm PS)
  thm-inPhysNPwCostGuards PS =
    (record
      { PW = physWitnessForThm PS
      ; wsize≤checkCost = ProofSystem.wsize≤checkCost PS
      } , tt)
