{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.ProofSearchGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; fst; snd; proj₁; proj₂)
open import Data.NatOrder using (_≤ℕ_; dec≤ℕ; z≤n; ≤ℕ-refl)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
open import LogOS.Domain.Complexity.Arithmetic using (pow)
import LogOS.Domain.Complexity.LanguageWitnessW as LWW
import LogOS.Domain.Complexity.PhysicsClassesWGraded as PCW
import LogOS.Domain.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
import LogOS.Domain.Complexity.PhysProofBridgeWGraded as PBW
import LogOS.Domain.Complexity.ProofSystem as PSCore

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

  thm-inPhysNPw
    : ∀ {P} (PS : ProofSystem P) → C.PhysNPw (Thm PS)
  thm-inPhysNPw {P} PS =
    (record
      { WS = record
          { W        = ProofSystem.Proof PS
          ; wsize    = ProofSystem.psize PS
          ; size     = size
          ; polyBound = ProofSystem.polyBound PS
          ; Check    = λ x p →
                        (LWW._≤ℕ_ (ProofSystem.psize PS p)
                                  (ProofSystem.polyBound PS (size x)))
                        × ProofSystem.Check PS x p
          ; decCheck = decCheck'
          ; sound    = λ x p pr → p , pr
          ; complete = λ x thm →
              let p  = proj₁ thm in
              let le = fst (proj₂ thm) in
              let ok = snd (proj₂ thm) in
              p , (le , (le , ok))
          }
      ; checkCost  = ProofSystem.checkCost PS
      ; checkBound = ProofSystem.checkBound PS
      ; polyCheck  = ProofSystem.polyCheck PS
      ; checkCost≤ = ProofSystem.checkCost≤ PS
      } , tt)
    where
      decCheck'
        : ∀ x p →
          ((LWW._≤ℕ_ (ProofSystem.psize PS p)
                     (ProofSystem.polyBound PS (size x)))
           × ProofSystem.Check PS x p)
          ⊎
          ¬ ((LWW._≤ℕ_ (ProofSystem.psize PS p)
                        (ProofSystem.polyBound PS (size x)))
              × ProofSystem.Check PS x p)
      decCheck' x p with dec≤ℕ (ProofSystem.psize PS p) (ProofSystem.polyBound PS (size x))
                         | ProofSystem.decCheck PS x p
      ... | inj₁ le | inj₁ ok = inj₁ (le , ok)
      ... | inj₁ le | inj₂ nok = inj₂ (λ pr → nok (snd pr))
      ... | inj₂ nle | _ = inj₂ (λ pr → nle (fst pr))

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
  thm-inPhysNPwG {P} PS =
    (record
      { WS = record
          { W        = ProofSystem.Proof PS
          ; wsize    = ProofSystem.psize PS
          ; size     = size
          ; polyBound = ProofSystem.polyBound PS
          ; Check    = λ x p →
                        (LWW._≤ℕ_ (ProofSystem.psize PS p)
                                  (ProofSystem.polyBound PS (size x)))
                        × ProofSystem.Check PS x p
          ; decCheck = decCheck'
          ; sound    = λ x p pr → p , pr
          ; complete = λ x thm →
              let p  = proj₁ thm in
              let le = fst (proj₂ thm) in
              let ok = snd (proj₂ thm) in
              p , (le , (le , ok))
          }
      ; checkCost   = ProofSystem.checkCost PS
      ; checkBoundG = λ n → gradeBound (ProofSystem.checkBound PS n)
      ; checkCost≤  = ProofSystem.checkCost≤ PS
      } , tt)
    where
      decCheck'
        : ∀ x p →
          ((LWW._≤ℕ_ (ProofSystem.psize PS p)
                     (ProofSystem.polyBound PS (size x)))
           × ProofSystem.Check PS x p)
          ⊎
          ¬ ((LWW._≤ℕ_ (ProofSystem.psize PS p)
                        (ProofSystem.polyBound PS (size x)))
              × ProofSystem.Check PS x p)
      decCheck' x p with dec≤ℕ (ProofSystem.psize PS p) (ProofSystem.polyBound PS (size x))
                         | ProofSystem.decCheck PS x p
      ... | inj₁ le | inj₁ ok = inj₁ (le , ok)
      ... | inj₁ le | inj₂ nok = inj₂ (λ pr → nok (snd pr))
      ... | inj₂ nle | _ = inj₂ (λ pr → nle (fst pr))

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
  thm-inPhysNPwCostGuards {P} PS =
    (record
      { PW = record
          { WS = record
              { W        = ProofSystem.Proof PS
              ; wsize    = ProofSystem.psize PS
              ; size     = size
              ; polyBound = ProofSystem.polyBound PS
              ; Check    = λ x p →
                            (LWW._≤ℕ_ (ProofSystem.psize PS p)
                                      (ProofSystem.polyBound PS (size x)))
                            × ProofSystem.Check PS x p
              ; decCheck = decCheck'
              ; sound    = λ x p pr → p , pr
              ; complete = λ x thm →
                  let p  = proj₁ thm in
                  let le = fst (proj₂ thm) in
                  let ok = snd (proj₂ thm) in
                  p , (le , (le , ok))
              }
          ; checkCost  = ProofSystem.checkCost PS
          ; checkBound = ProofSystem.checkBound PS
          ; polyCheck  = ProofSystem.polyCheck PS
          ; checkCost≤ = ProofSystem.checkCost≤ PS
          }
      ; wsize≤checkCost = ProofSystem.wsize≤checkCost PS
      } , tt)
    where
      decCheck'
        : ∀ x p →
          ((LWW._≤ℕ_ (ProofSystem.psize PS p)
                     (ProofSystem.polyBound PS (size x)))
           × ProofSystem.Check PS x p)
          ⊎
          ¬ ((LWW._≤ℕ_ (ProofSystem.psize PS p)
                        (ProofSystem.polyBound PS (size x)))
              × ProofSystem.Check PS x p)
      decCheck' x p with dec≤ℕ (ProofSystem.psize PS p) (ProofSystem.polyBound PS (size x))
                         | ProofSystem.decCheck PS x p
      ... | inj₁ le | inj₁ ok = inj₁ (le , ok)
      ... | inj₁ le | inj₂ nok = inj₂ (λ pr → nok (snd pr))
      ... | inj₂ nle | _ = inj₂ (λ pr → nle (fst pr))
