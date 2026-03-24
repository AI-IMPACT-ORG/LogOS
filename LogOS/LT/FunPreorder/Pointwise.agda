{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.FunPreorder.Pointwise where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Generic pointwise lifts for function-space preorders.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.FunPreorder using (DFunPreorder; FunPreorder)
open import LogOS.LT.Flow using (GuardedClosure; Flow; mono; infl; idemp-lax)
open import LogOS.LT.Sup.FinSup using (FinSup)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO; Directedω)
open import LogOS.LT.Stage.SuccessorChain using (Stageω)

pointwiseClosure
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → ((i : I) → GuardedClosure (O i))
  → GuardedClosure (DFunPreorder I O)
pointwiseClosure {I = I} {O = O} GC =
  record
    { Flow = λ F i → Flow (GC i) (F i)
    ; mono = λ {F} {G} FG i → mono (GC i) (FG i)
    ; infl = λ F i → infl (GC i) (F i)
    ; idemp-lax = λ F i → idemp-lax (GC i) (F i)
    }

pointwiseClosureUniform
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → GuardedClosure O
  → GuardedClosure (FunPreorder I O)
pointwiseClosureUniform GC = pointwiseClosure (λ _ → GC)

pointwiseFinSup
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → ((i : I) → FinSup (O i))
  → FinSup (DFunPreorder I O)
pointwiseFinSup {I = I} {O = O} FS =
  record
    { _⊔ᶠ_ = λ F G i → FinSup._⊔ᶠ_ (FS i) (F i) (G i)
    ; ⊥ᶠ = λ i → FinSup.⊥ᶠ (FS i)
    ; ⊥ᶠ-least = λ F i → FinSup.⊥ᶠ-least (FS i) (F i)
    ; ⊔ᶠ-ub₁ = λ F G i → FinSup.⊔ᶠ-ub₁ (FS i) (F i) (G i)
    ; ⊔ᶠ-ub₂ = λ F G i → FinSup.⊔ᶠ-ub₂ (FS i) (F i) (G i)
    ; ⊔ᶠ-least = λ {F} {G} {H} FH GH i → FinSup.⊔ᶠ-least (FS i) (FH i) (GH i)
    }

pointwiseFinSupUniform
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → FinSup O
  → FinSup (FunPreorder I O)
pointwiseFinSupUniform FS = pointwiseFinSup (λ _ → FS)

pointwiseSigmaDCPO
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → ((i : I) → SigmaDCPO (O i))
  → SigmaDCPO (DFunPreorder I O)
pointwiseSigmaDCPO {I = I} {O = O} SD =
  record
    { supσ = λ s dir i → SigmaDCPO.supσ (SD i) (λ n → s n i) (dirAt dir i)
    ; ubσ = λ s dir n i → SigmaDCPO.ubσ (SD i) (λ m → s m i) (dirAt dir i) n
    ; leastσ = λ s dir x xubs i →
        SigmaDCPO.leastσ (SD i) (λ n → s n i) (dirAt dir i) (x i) (λ n → xubs n i)
    }
  where
    dirAt
      : ∀ {s : Stageω → Con (DFunPreorder I O)}
      → Directedω (DFunPreorder I O) s
      → (i : I)
      → Directedω (O i) (λ n → s n i)
    dirAt dir i m n with dir m n
    ... | k , (sm≤sk , sn≤sk) = k , (sm≤sk i , sn≤sk i)

pointwiseSigmaDCPOUniform
  : ∀ {ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → SigmaDCPO O
  → SigmaDCPO (FunPreorder I O)
pointwiseSigmaDCPOUniform SD = pointwiseSigmaDCPO (λ _ → SD)
