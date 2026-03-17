{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Definitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Definitional/bookkeeping equalities for stack packaging.

open import LogOS.Prelude
open import LogOS.LT.View.Family using (bundleView; bundleKernel)
open import LogOS.LT.Stack.Core using
  ( Stack
  ; Op
  ; Code
  ; StackCode
  ; mkStackCode
  ; opIdx
  ; code
  ; stackView
  ; stackAsFamily
  ; stackKernel
  )

stackView≡bundleView
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
    (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → stackView S ≡ bundleView (stackAsFamily S)
stackView≡bundleView _ = refl

stackKernel≡bundleKernel
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
    (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → stackKernel S ≡ bundleKernel (stackAsFamily S)
stackKernel≡bundleKernel _ = refl

opIdx-mkStackCode
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    (o : Op S)
    (γ : Code S o)
  → opIdx (mkStackCode {S = S} o γ) ≡ o
opIdx-mkStackCode {S = S} _ _ = refl

code-mkStackCode
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    (o : Op S)
    (γ : Code S o)
  → code (mkStackCode {S = S} o γ) ≡ γ
code-mkStackCode {S = S} _ _ = refl
