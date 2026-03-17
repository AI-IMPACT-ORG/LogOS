{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Definitional where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Kernel using (CodePreorder; ObservedCodePreorder)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using (ShadowByView)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core using
  ( BoundaryKernelAt
  ; BoundaryHomPreorder
  )

boundaryHomPreorder-isObservedCodePreorderDef
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    (S : ShadowByView C O)
    {A B : TwoCellOps.Obj C}
  → BoundaryHomPreorder S A B
    ≡ ObservedCodePreorder (BoundaryKernelAt S {A} {B})
boundaryHomPreorder-isObservedCodePreorderDef _ = refl

boundaryHomPreorder-isCodePreorder
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
    (S : ShadowByView C O)
    {A B : TwoCellOps.Obj C}
  → BoundaryHomPreorder S A B
    ≡ CodePreorder (BoundaryKernelAt S {A} {B})
boundaryHomPreorder-isCodePreorder _ = refl
