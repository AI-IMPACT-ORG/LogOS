{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Sup.AbstractGeneratedClosure where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Generated closures by ω-iteration + joins.
--
-- This is the LT-core packaging of the recurring Kleene-generation pattern:
-- - start from a seed/base observable,
-- - close it under a finite family of monotone inflationary components,
-- - and recover a guarded closure / effectivity doctrine from the generated μ.

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc)
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; MonoOn; refl⊑)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Effectivity using (Effectivity)
open import LogOS.LT.Sup.FinSup using (FinSup; hasBottomFromFinSup)
open import LogOS.LT.Sup.AbstractSigmaDCPO using (SigmaDCPO; SigmaContinuous)
import LogOS.LT.Sup.AbstractKleene as Kleene

record Component {ℓCon ℓRel : Level} (CP : ConPreorder ℓCon ℓRel)
  : Set (lsuc (ℓCon ⊔ ℓRel)) where
  field
    op   : Con CP → Con CP
    mono : MonoOn CP op
    infl : ∀ c → _⊑_ CP c (op c)

open Component public

module GeneratedClosureLocal
  {ℓCon ℓRel : Level}
  {CP : ConPreorder ℓCon ℓRel}
  (FS : FinSup CP)
  (SD : SigmaDCPO CP)
  (Cs : List (Component CP))
  where

  open FinSup FS
  module R = LogOS.Prelude.RefinementKit.Reasoning CP
  open R

  joinComponents : List (Component CP) → Con CP → Con CP
  joinComponents []        c = ⊥ᶠ
  joinComponents (C ∷ Cs) c = op C c ⊔ᶠ joinComponents Cs c

  joinComponents-mono
    : ∀ (Cs : List (Component CP))
    → MonoOn CP (joinComponents Cs)
  joinComponents-mono [] le = ⊥ᶠ-least _
  joinComponents-mono (C ∷ Cs) le =
    LogOS.LT.Sup.FinSup.FinSupLocal.⊔ᶠ-mono FS (mono C le) (joinComponents-mono Cs le)

  generationStep : Con CP → Con CP → Con CP
  generationStep base c = base ⊔ᶠ (c ⊔ᶠ joinComponents Cs c)

  module Generated (step-cont : ∀ base → SigmaContinuous CP SD (generationStep base)) where
    private
      HB = hasBottomFromFinSup FS

    module K (base : Con CP) = Kleene.KleeneLocal HB SD (generationStep base) (step-cont base)

    generated : Con CP → Con CP
    generated base = K.μ base

    generated-prefix
      : ∀ base → _⊑_ CP (generationStep base (generated base)) (generated base)
    generated-prefix base = K.μ-prefix base

    step-mono-base
      : ∀ {base base'} → _⊑_ CP base base' → ∀ c → _⊑_ CP (generationStep base c) (generationStep base' c)
    step-mono-base base≤base' c =
      LogOS.LT.Sup.FinSup.FinSupLocal.⊔ᶠ-mono FS base≤base' (refl⊑ CP)

    generated-mono
      : MonoOn CP generated
    generated-mono {x = base} {y = base'} base≤base' =
      K.μ-leastPrefix base (generated base') stepBase≤
      where
        stepBase≤ : _⊑_ CP (generationStep base (generated base')) (generated base')
        stepBase≤ =
          begin⊑
            generationStep base (generated base') ⊑⟨ step-mono-base base≤base' (generated base') ⟩
            generationStep base' (generated base') ⊑⟨ generated-prefix base' ⟩
            generated base' ∎⊑

    generated-infl
      : ∀ base → _⊑_ CP base (generated base)
    generated-infl base =
      begin⊑
        base ⊑⟨ ⊔ᶠ-ub₁ base (HasBottom.⊥ᵇ HB ⊔ᶠ joinComponents Cs (HasBottom.⊥ᵇ HB)) ⟩
        generationStep base (HasBottom.⊥ᵇ HB)
          ⊑⟨ SigmaDCPO.ubσ SD (K.iter⊥ base) (K.iter⊥-dir base) (suc zero) ⟩
        generated base ∎⊑
      where
        open import LogOS.LT.Sup.FinSup using (HasBottom)

    joinComponents≤generated
      : ∀ base → _⊑_ CP (joinComponents Cs (generated base)) (generated base)
    joinComponents≤generated base =
      begin⊑
        joinComponents Cs (generated base)
          ⊑⟨ ⊔ᶠ-ub₂ (generated base) (joinComponents Cs (generated base)) ⟩
        (generated base ⊔ᶠ joinComponents Cs (generated base))
          ⊑⟨ ⊔ᶠ-ub₂ base (generated base ⊔ᶠ joinComponents Cs (generated base)) ⟩
        generationStep base (generated base) ⊑⟨ generated-prefix base ⟩
        generated base ∎⊑

    generated-idemp-lax
      : ∀ base → _⊑_ CP (generated (generated base)) (generated base)
    generated-idemp-lax base =
      K.μ-leastPrefix (generated base) (generated base) step≤
      where
        step≤ : _⊑_ CP (generationStep (generated base) (generated base)) (generated base)
        step≤ =
          ⊔ᶠ-least
            (refl⊑ CP)
            (⊔ᶠ-least
              (refl⊑ CP)
              (joinComponents≤generated base))

    generatedClosure : GuardedClosure CP
    generatedClosure =
      record
        { Flow      = generated
        ; mono      = generated-mono
        ; infl      = generated-infl
        ; idemp-lax = generated-idemp-lax
        }

    generatedEffectivity : Effectivity CP
    generatedEffectivity = record { GC = generatedClosure }
