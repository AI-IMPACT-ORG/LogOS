{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Extend where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Reusable “boring glue” for extending a stack vocabulary over the same boundary.
--
-- Many application packs build a base stack and then extend it with a small
-- number of additional operations (e.g. ZF → ZFC adds a choice transformer).
-- This module factors out the canonical extension + inclusion maps.

open import LogOS.Prelude
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Hom.Core using (KernelHom)
import LogOS.LT.Hom.Strictification as StrictHom

open import LogOS.LT.Stack.Core using
  ( Stack
  ; bnd
  ; Op
  ; Code
  ; op
  ; stackKernel
  )
import LogOS.LT.Stack.Strictification as StrictStack
open import LogOS.LT.Stack.Program using
  ( SameBoundaryProgramMap
  ; programKernel
  )

-- Canonical inclusion of the base stack into the extended stack (strict, same boundary).
extendStackMap
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓNewOp ℓNewCode : Level}
  → (S₀ : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → (NewOp : Set ℓNewOp)
  → (NewCode : NewOp → Set ℓNewCode)
  → ((o : NewOp) → View (NewCode o) (bnd S₀))
  → StrictStack.SameBoundaryStackMap≡
      {ℓSrcOp = ℓOp}
      {ℓSrcCode = ℓCode}
      {ℓTgtOp = ℓOp ⊔ ℓNewOp}
      {ℓTgtCode = ℓCode ⊔ ℓNewCode}
      (bnd S₀)
extendStackMap {ℓCode = ℓCode} {ℓNewCode = ℓNewCode} S₀ NewOp NewCode newView =
  record
    { SourceOp = Op S₀
    ; TargetOp = Op S₀ ⊎ NewOp
    ; SourceCode = Code S₀
    ; TargetCode =
        λ where
          (inj₁ o) → Lift ℓNewCode (Code S₀ o)
          (inj₂ o) → Lift ℓCode (NewCode o)
    ; sourceView = op S₀
    ; targetView =
        λ where
          (inj₁ o) →
            record
              { μ = λ γ → μ (op S₀ o) (lower γ) }
          (inj₂ o) →
            record
              { μ = λ γ → μ (newView o) (lower γ) }
    ; mapOp = inj₁
    ; mapCodeAt = λ _ γ → lift γ
    ; mapCodeAt-preserves = λ _ _ → refl
    }

-- Extend a stack by adding a new family of operations over the same boundary.
--
-- Defined via `extendStackMap` to make the inclusion-induced kernel embeddings
-- definitionally align (avoids duplicated case splits).
extendStack
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓNewOp ℓNewCode : Level}
  → (S₀ : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → (NewOp : Set ℓNewOp)
  → (NewCode : NewOp → Set ℓNewCode)
  → ((o : NewOp) → View (NewCode o) (bnd S₀))
  → Stack {ℓB} {ℓRel} {ℓOp ⊔ ℓNewOp} {ℓCode ⊔ ℓNewCode}
extendStack S₀ NewOp NewCode newView =
  StrictStack.SameBoundaryStackMap≡.Target (extendStackMap S₀ NewOp NewCode newView)

-- Program-level inclusion along the canonical stack inclusion.
extendProgramMap
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓNewOp ℓNewCode : Level}
  → (S₀ : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → (NewOp : Set ℓNewOp)
  → (NewCode : NewOp → Set ℓNewCode)
  → (newView : (o : NewOp) → View (NewCode o) (bnd S₀))
  → SameBoundaryProgramMap (StrictStack.homFromMap (extendStackMap S₀ NewOp NewCode newView))
extendProgramMap S₀ NewOp NewCode newView =
  record
    { unmapCode = λ _ γ → lower γ
    ; unmapCode-mapCode = λ _ _ → refl
    }

-- Kernel embeddings induced by the canonical inclusion.
stackKernel↪
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓNewOp ℓNewCode : Level}
  → (S₀ : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → (NewOp : Set ℓNewOp)
  → (NewCode : NewOp → Set ℓNewCode)
  → (newView : (o : NewOp) → View (NewCode o) (bnd S₀))
  → KernelHom (stackKernel S₀) (stackKernel (extendStack S₀ NewOp NewCode newView))
stackKernel↪ S₀ NewOp NewCode newView =
  StrictHom.strict→approx
    (StrictStack.SameBoundaryStackMap≡.stackKernelHom≡ (extendStackMap S₀ NewOp NewCode newView))

programKernel↪
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓNewOp ℓNewCode : Level}
  → (S₀ : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → (NewOp : Set ℓNewOp)
  → (NewCode : NewOp → Set ℓNewCode)
  → (newView : (o : NewOp) → View (NewCode o) (bnd S₀))
  → KernelHom (programKernel S₀) (programKernel (extendStack S₀ NewOp NewCode newView))
programKernel↪ S₀ NewOp NewCode newView =
  SameBoundaryProgramMap.programKernelHom (extendProgramMap S₀ NewOp NewCode newView)
