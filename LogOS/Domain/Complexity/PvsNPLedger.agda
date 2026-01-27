{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PvsNPLedger where

-- P vs NP in LogOS is an *interface ledger* / *reverse-mathematics template*:
-- it isolates the exact interfaces needed to state the classical P/NP
-- definitions and relate them to kernel-derived “verification vs search”
-- pipelines, without claiming a separation proof.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; ≤ℕ-refl)

open import LogOS.QAdapters.QNat using (QNat)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Graded

open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PhysicsClassesWGraded as PCW
import LogOS.Domain.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
import LogOS.Domain.Complexity.LanguageWitness as LW
import LogOS.Domain.Complexity.LanguageWitnessW as LWW
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TR

-- Classical, literature-aligned P/NP interface:
-- a language is an input predicate, and P/NP are defined via poly-time deciders
-- and poly-bounded witness verifiers. This is a lightweight rename of the
-- PhysicsClassesW/CostGuards interfaces with “cost” interpreted as time.
--
-- Instantiating cost/checkCost with a kernel-native graded route recovers the
-- textbook definitions once you supply a concrete computation model.

module For {ℓI ℓW ℓ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           where

  module Core = PCW.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} Input size Pℕ
                 QNat (QAdapter.τ QNat)
  open Core public
    renaming
      ( PhysDecider     to PolyTimeDecider
      ; PhysP           to InP
      ; PhysWitnessW    to PolyTimeVerifierW
      ; PhysNPw         to InNP
      ; PhysSeparationW to SeparationW
      ; notPhysP        to notInP
      )

  module CostGuards = PCWCG.For {ℓI = ℓI} {ℓW = ℓW} {ℓ = ℓ} Input size Pℕ
                        QNat (QAdapter.τ QNat)
  open CostGuards public hiding (Language)
    renaming
      ( PhysDeciderCostGuards   to PolyTimeDeciderCostGuards
      ; PhysPCostGuards         to InP_CostGuards
      ; PhysWitnessWCostGuards  to PolyTimeVerifierWCostGuards
      ; PhysNPwCostGuards       to InNP_CostGuards
      ; forgetP                 to forgetP_CostGuards
      ; forgetNPw               to forgetNPw_CostGuards
      ; notPhysPCostGuards      to notInP_CostGuards
      )

-- Reduction from the graded truth-route (correctness-carrying) to the
-- classical interface above.

module FromTruthRoute
  {ℓ ℓI ℓP : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (IsPoly : (ℕ → ℕ) → Set ℓP)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (WSize : GradedKernel.Code K → ℕ)
  (Pℕ : PolyPred)
  (polyOk : ∀ {p : ℕ → ℕ} → IsPoly p → PolyPred.isPoly Pℕ p)
  where

  module R = TR.UniformNatFromRuns K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
  module W = R.WithWitnessSize WSize

  module ForLanguage {ℓL : Level} (L : R.Language ℓL) where
    module C = For {ℓI = ℓI} {ℓW = ℓ} {ℓ = ℓ ⊔ ℓL} Input Size Pℕ

    fromInP : R.InP {ℓL = ℓL} L → C.InP L
    fromInP P =
      let open R.InP P
          decide : Input → Set (ℓ ⊔ ℓL)
          decide x = Acc (R.Flow (gradeBound (tBound (Size x))) (R.encodeI x))
          D : LW.DeciderI Input L
          D = record
            { decide = decide
            ; total  = λ x → decAcc (R.Flow (gradeBound (tBound (Size x))) (R.encodeI x))
            ; sound  = λ x d → Prop.from (correct x) d
            ; comp   = λ x px → Prop.to (correct x) px
            }
      in
      ( record
          { D         = D
          ; cost      = λ x → tBound (Size x)
          ; bound     = tBound
          ; polyBound = polyOk polyT
          ; cost≤     = λ _ → ≤ℕ-refl
          }
      , tt
      )

    fromInNP : W.InNP {ℓL = ℓL} L → C.InNP L
    fromInNP NP =
      ( record
          { WS         = WS
          ; checkCost  = λ x w → tBound (Size x)
          ; checkBound = tBound
          ; polyCheck  = polyOk polyT
          ; checkCost≤ = λ _ _ → ≤ℕ-refl
          }
      , tt
      )
      where
        open W.InNP NP

        WS : LWW.WitnessSystemW {ℓI = ℓI} {ℓW = ℓ} {ℓ = ℓ ⊔ ℓL} Input L
        WS = record
          { W         = λ x → Σ (GradedKernel.Code K) (λ w → WSize w ≤ℕ wBound (Size x))
          ; wsize     = λ {x} (w , _) → WSize w
          ; size      = Size
          ; polyBound = wBound
          ; Check     = Check
          ; decCheck  = decCheck
          ; sound     = sound
          ; complete  = complete
          }
          where
            Check : ∀ x → Σ (GradedKernel.Code K) (λ w → WSize w ≤ℕ wBound (Size x)) → Set (ℓ ⊔ ℓL)
            Check x (w , _) =
              Acc (R.Flow (gradeBound (tBound (Size x))) (R.VerObsWith x w))

            decCheck : ∀ x w → Check x w ⊎ ¬ Check x w
            decCheck x (w , _) =
              decAcc (R.Flow (gradeBound (tBound (Size x))) (R.VerObsWith x w))

            sound : ∀ x w → Check x w → L x
            sound x (w , le) acc =
              Prop.from (correct x) (w , (le , acc))

            complete
              : ∀ x → L x →
                Σ (Σ (GradedKernel.Code K) (λ w → WSize w ≤ℕ wBound (Size x)))
                  (λ w → (WSize (proj₁ w) ≤ℕ wBound (Size x)) × Check x w)
            complete x px with Prop.to (correct x) px
            ... | w , (le , ok) = (w , le) , (le , ok)

    -- Alignment pack: explicitly record the literature mapping (no extra axioms).
    record Alignment : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓL ⊔ ℓP))) where
      field
        inP  : R.InP {ℓL = ℓL} L → C.InP L
        inNP : W.InNP {ℓL = ℓL} L → C.InNP L

    alignment : Alignment
    alignment = record { inP = fromInP ; inNP = fromInNP }
