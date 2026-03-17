{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Support.TrivialBoundaryWorld where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps
  ; TwoCellOpsLaws
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core using
  ( BoundaryPresentation
  ; CompleteBoundaryPresentation
  ; canonicalBoundaryPresentation
  ; canonicalCompleteBoundaryPresentation
  )

ops : TwoCellOps lzero lzero lzero
ops =
  record
    { Obj = ⊤
    ; Hom₁ = λ _ _ → ⊤
    ; Hom₂ = λ _ _ → ⊤
    ; id1 = tt
    ; _∘1_ = λ _ _ → tt
    ; id2 = tt
    ; _∙2_ = λ _ _ → tt
    ; whiskerL2 = λ _ → tt
    ; whiskerR2 = λ _ → tt
    }

laws : TwoCellOpsLaws ops
laws =
  record
    { id-left = λ _ → (tt , tt)
    ; id-right = λ _ → (tt , tt)
    ; assoc = λ _ _ _ → (tt , tt)
    }

B : BicatW lzero lzero lzero
B = record { ops = ops ; laws = laws }

O
  : TwoCellOps.Obj (BicatW→TwoCellOps B)
  → TwoCellOps.Obj (BicatW→TwoCellOps B)
  → ConPreorder lzero lzero
O _ _ = UnitPreorder₀

S : ShadowByView (BicatW→TwoCellOps B) O
S =
  record
    { μ = λ {A} {B} → record { μ = λ _ → tt }
    ; soundμ = λ _ → tt
    ; μ-whiskerL = λ _ → tt
    ; μ-whiskerR = λ _ → tt
    }

P : BoundaryPresentation S
P = canonicalBoundaryPresentation S

CP : CompleteBoundaryPresentation P
CP = canonicalCompleteBoundaryPresentation S
