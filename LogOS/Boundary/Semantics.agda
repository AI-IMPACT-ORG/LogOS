{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.Semantics where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Boundary.IO

-- A generic bridge from H-tier satisfaction to an external boundary logic.
-- Provide a BoundaryIO and an interpretation of boundary constraints into
-- external formulas with a satisfaction equivalence (↔); derive a transport lemma.

record BoundarySemantics {ℓ ℓForm}
                        (Sig : LogOSSignature ℓ)
                        (Q   : QAdapter ℓ)
                        (W   : Worlds.WorldH Sig Q)
                        (BB  : BulkBoundary ℓ)
                        (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                        (B   : BoundaryIO Sig Q W BB H)
                        : Set (lsuc (ℓ ⊔ ℓForm)) where
  open LogOSSignature Sig
  module HT = Truth.HomotypicalTruth Sig Q W
  open BulkBoundary BB
  field
    Form  : Set ℓForm
    SatF  : ∂Cosp → Form → Set ℓ
    Interp : Con_bnd → Form
    Sat∂≈F : ∀ p c → Prop._↔_ (BoundaryIO.Sat∂ B p c) (SatF p (Interp c))

  -- Derived: direct H-tier ↔ external form equivalence (via the boundary).

  H↔Form
    : ∀ (w : Cosp) (c : Con_bnd)
    → Prop._↔_ (HT.HLayer.Sat_H H w c)
               (SatF (BoundaryIO.to∂ B w) (Interp c))
  H↔Form w c =
    Prop.↔-trans
      (BoundaryIO.sat-coh B w c)
      (Sat∂≈F (BoundaryIO.to∂ B w) c)

  H→Form
    : ∀ (w : Cosp) (c : Con_bnd)
    → HT.HLayer.Sat_H H w c
    → SatF (BoundaryIO.to∂ B w) (Interp c)
  H→Form w c = Prop._↔_.to (H↔Form w c)

  Form→H
    : ∀ (w : Cosp) (c : Con_bnd)
    → SatF (BoundaryIO.to∂ B w) (Interp c)
    → HT.HLayer.Sat_H H w c
  Form→H w c = Prop._↔_.from (H↔Form w c)
