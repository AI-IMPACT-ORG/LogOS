{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.VacuityGuards where

-- Vacuity guards for ports/adapters: guard against trivial satisfaction and
-- constant adapters that erase boundary distinctions.

open import LogOS.Prelude
import LogOS.Syntax.Prop as Prop
open import LogOS.Syntax.Prop using (¬_)

import LogOS.Minimal.View as View

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port
open import LogOS.Ports.Semantic.Interoperability using (PortAdapter)

record PortVacuityGuards
  {ℓ : Level}
  {ℓForm : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  : Set (lsuc (ℓ ⊔ ℓForm)) where
  open LogOSSignature Sig
  open BoundaryIO B
  open BoundaryPort P
  field
    p : ∂Cosp
    φ₀ φ₁ : Form
    sat₀ : SatF p φ₀
    unsat₁ : ¬ (SatF p φ₁)

  -- Derived: formula-level observational distinguishability.
  obsDistinctF : ¬ (Prop.ObsEqOn SatF φ₀ φ₁)
  obsDistinctF eq = unsat₁ (Prop.to (eq p) sat₀)

  obsDistinct≈F : ¬ (View.Obs≈ SatF φ₀ φ₁)
  obsDistinct≈F (φ₀≤φ₁ , _) = unsat₁ (φ₀≤φ₁ p sat₀)

  -- Derived: the two formulas are definitional distinct (representation-level).
  φ₀≢φ₁ : ¬ (φ₀ ≡ φ₁)
  φ₀≢φ₁ eq = unsat₁ (subst (SatF p) eq sat₀)

  -- Derived: boundary imports are definitional distinct.
  import-distinct : ¬ (Import φ₀ ≡ Import φ₁)
  import-distinct eq =
    let
      sat₀∂  = Prop.to (SatF≈∂ p φ₀) sat₀
      sat₁∂  = subst (Sat∂ p) eq sat₀∂
      sat₁   = Prop.from (SatF≈∂ p φ₁) sat₁∂
    in
    unsat₁ sat₁

  -- Derived: boundary imports are observationally distinguishable (semantics-level).
  import-obsDistinct : ¬ (Import φ₀ ≈∂[ B ] Import φ₁)
  import-obsDistinct eq =
    let
      sat₀∂ = Prop.to (SatF≈∂ p φ₀) sat₀
      sat₁∂ = fst eq p sat₀∂
      sat₁  = Prop.from (SatF≈∂ p φ₁) sat₁∂
    in
    unsat₁ sat₁

record AdapterVacuityGuards
  {ℓ : Level}
  {ℓForm₁ ℓForm₂ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  (A : PortAdapter B P₁ P₂)
  : Set (lsuc (ℓ ⊔ ℓForm₁ ⊔ ℓForm₂)) where
  open LogOSSignature Sig
  private
    module P1 = BoundaryPort P₁
  open PortAdapter A
  field
    p : ∂Cosp
    φ₀ φ₁ : P1.Form
    sat₀ : P1.SatF p φ₀
    unsat₁ : ¬ (P1.SatF p φ₁)
    map-distinct : ¬ (map φ₀ ≡ map φ₁)

  private
    module P2 = BoundaryPort P₂

  -- Derived: definitional distinctness on the source side (representation-level).
  φ₀≢φ₁ : ¬ (φ₀ ≡ φ₁)
  φ₀≢φ₁ eq = unsat₁ (subst (P1.SatF p) eq sat₀)

  -- Derived: satisfaction witnesses transport along the adapter.
  sat₀₂ : P2.SatF p (map φ₀)
  sat₀₂ = Prop.to (preserves-Sat p φ₀) sat₀

  unsat₁₂ : ¬ (P2.SatF p (map φ₁))
  unsat₁₂ sat = unsat₁ (Prop.from (preserves-Sat p φ₁) sat)

  -- Derived: target formulas are observationally distinguishable.
  map-obsDistinctF : ¬ (Prop.ObsEqOn P2.SatF (map φ₀) (map φ₁))
  map-obsDistinctF eq = unsat₁₂ (Prop.to (eq p) sat₀₂)

  map-obsDistinct≈F : ¬ (View.Obs≈ P2.SatF (map φ₀) (map φ₁))
  map-obsDistinct≈F (mφ₀≤mφ₁ , _) = unsat₁₂ (mφ₀≤mφ₁ p sat₀₂)

  -- Derived: boundary imports of the mapped formulas remain distinguishable.
  import-distinct₂ : ¬ (P2.Import (map φ₀) ≡ P2.Import (map φ₁))
  import-distinct₂ eq =
    let
      sat₀∂  = Prop.to (P2.SatF≈∂ p (map φ₀)) sat₀₂
      sat₁∂  = subst (BoundaryIO.Sat∂ B p) eq sat₀∂
      sat₁   = Prop.from (P2.SatF≈∂ p (map φ₁)) sat₁∂
    in
    unsat₁₂ sat₁

  import-obsDistinct₂ : ¬ (P2.Import (map φ₀) ≈∂[ B ] P2.Import (map φ₁))
  import-obsDistinct₂ eq =
    let
      sat₀∂ = Prop.to (P2.SatF≈∂ p (map φ₀)) sat₀₂
      sat₁∂ = fst eq p sat₀∂
      sat₁  = Prop.from (P2.SatF≈∂ p (map φ₁)) sat₁∂
    in
    unsat₁₂ sat₁
