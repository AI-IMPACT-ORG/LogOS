{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.Port where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Boundary.IO
open import LogOS.Boundary.Semantics

-- Boundary observational equivalence induced by a `BoundaryIO`.

infix 4 _≈∂[_]_
_≈∂[_]_ : ∀ {ℓ}
          {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
          {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
          {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
        → BulkBoundary.Con_bnd BB
        → BoundaryIO Sig Q W BB H
        → BulkBoundary.Con_bnd BB
        → Set ℓ
_≈∂[_]_ c B d = Prop.ObsEqOn (BoundaryIO.Sat∂ B) c d

-- More name-aligned alias (cf. `LogOS.Computation.Scheme.ObsEq` / OS theorems).

ObsEq∂ : ∀ {ℓ}
         {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
         {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
       → BoundaryIO Sig Q W BB H
       → BulkBoundary.Con_bnd BB
       → BulkBoundary.Con_bnd BB
       → Set ℓ
ObsEq∂ B c d = c ≈∂[ B ] d

-- Consistent alias for boundary constraints (cf. PresentationC.ObsEqCon).

ObsEqBnd : ∀ {ℓ}
           {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
           {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
           {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
         → BoundaryIO Sig Q W BB H
         → BulkBoundary.Con_bnd BB
         → BulkBoundary.Con_bnd BB
         → Set ℓ
ObsEqBnd = ObsEq∂

ObsLe∂
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → BoundaryIO Sig Q W BB H
  → BulkBoundary.Con_bnd BB
  → BulkBoundary.Con_bnd BB
  → Set ℓ
ObsLe∂ B c d = Prop.ObsLeOn (BoundaryIO.Sat∂ B) c d

ObsLeBnd
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → BoundaryIO Sig Q W BB H
  → BulkBoundary.Con_bnd BB
  → BulkBoundary.Con_bnd BB
  → Set ℓ
ObsLeBnd = ObsLe∂

ObsBndPreorder
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → ConPreorder ℓ
ObsBndPreorder {BB = BB} B =
  let open BulkBoundary BB in
  record
    { Con = Con_bnd
    ; _⊑_ = ObsLe∂ B
    ; refl = λ {c} p sat → sat
    ; trans = λ cd de p sat → de p (cd p sat)
    }

Respects≈∂[_] : ∀ {ℓ}
                {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
                {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
              → (B : BoundaryIO Sig Q W BB H)
              → (BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB)
              → Set ℓ
Respects≈∂[ B ] F = Prop.RespectsObsEqOn (BoundaryIO.Sat∂ B) F

RespectsObsEqBnd
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → (BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB)
  → Set ℓ
RespectsObsEqBnd B F = Respects≈∂[ B ] F

-- A boundary endomap packaged together with its observational extensionality.
--
-- This is a convenience wrapper for the common pattern “F plus Respects≈∂[B] F”.
record ObsEndo∂
  {ℓ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  : Set (lsuc ℓ) where
  open BulkBoundary BB
  field
    fn       : Con_bnd → Con_bnd
    respects : Respects≈∂[ B ] fn

module ObsEq∂Kit
  {ℓ}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  where

  open Prop.ObsEqKit (Prop.obsEqKit (BoundaryIO.Sat∂ B)) public

≈∂-refl
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → (c : BulkBoundary.Con_bnd BB)
  → c ≈∂[ B ] c
≈∂-refl B c = ObsEq∂Kit.reflEq B c

≈∂-sym
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → {B : BoundaryIO Sig Q W BB H}
  → {c d : BulkBoundary.Con_bnd BB}
  → c ≈∂[ B ] d
  → d ≈∂[ B ] c
≈∂-sym {B = B} eq = ObsEq∂Kit.symEq B eq

≈∂-trans
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → {B : BoundaryIO Sig Q W BB H}
  → {a b c : BulkBoundary.Con_bnd BB}
  → a ≈∂[ B ] b
  → b ≈∂[ B ] c
  → a ≈∂[ B ] c
≈∂-trans {B = B} ab bc = ObsEq∂Kit.transEq B ab bc

≈∂↔ObsLe
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → {c d : BulkBoundary.Con_bnd BB}
  → Prop._↔_
      (c ≈∂[ B ] d)
      (Prop._∧_ (ObsLe∂ B c d) (ObsLe∂ B d c))
≈∂↔ObsLe B {c} {d} =
  Prop.ObsEqOn↔ObsLeOn {Sat = BoundaryIO.Sat∂ B} {x = c} {y = d}

mono-ObsBnd-respects≈∂
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → {B : BoundaryIO Sig Q W BB H}
  → {F : BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB}
  → MonoOn (ObsBndPreorder B) F
  → Respects≈∂[ B ] F
mono-ObsBnd-respects≈∂ {B = B} monoF eq =
  Prop._↔_.from (≈∂↔ObsLe B)
    (monoOn-respects≈ {CP = ObsBndPreorder B} monoF
      (Prop._↔_.to (≈∂↔ObsLe B) eq))

-- External boundary “port”: a boundary semantics (export) plus an import leg.
--
-- This is intentionally minimal: it does not assume any syntactic completeness
-- or definitional equalities—only satisfaction equivalences.

record BoundaryPort {ℓ ℓForm}
                    (Sig : LogOSSignature ℓ)
                    (Q   : QAdapter ℓ)
                    (W   : Worlds.WorldH Sig Q)
                    (BB  : BulkBoundary ℓ)
                    (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                    (B   : BoundaryIO Sig Q W BB H)
                    : Set (lsuc (ℓ ⊔ ℓForm)) where
  open BulkBoundary BB
  field
    Sem : BoundarySemantics {ℓForm = ℓForm} Sig Q W BB H B
  open BoundarySemantics Sem public
  field
    Import : Form → Con_bnd
    SatF≈∂ : ∀ p φ → Prop._↔_ (SatF p φ) (BoundaryIO.Sat∂ B p (Import φ))

  -- Derived: lifting a boundary endomap to a formula endomap through the port.

  Extend : (Con_bnd → Con_bnd) → Form → Form
  Extend F φ = Interp (F (Import φ))

  -- Derived: lifting a boundary endomap preserves satisfaction when the
  -- underlying boundary semantics is sound for that endomap.
  Extend-preserves-Sat
    : ∀ (F : Con_bnd → Con_bnd)
    → (pres : ∀ p c → BoundaryIO.Sat∂ B p c → BoundaryIO.Sat∂ B p (F c))
    → ∀ p φ → SatF p φ → SatF p (Extend F φ)
  Extend-preserves-Sat F pres p φ satF =
    let
      sat∂  = Prop.to (SatF≈∂ p φ) satF
      sat∂' = pres p (Import φ) sat∂
    in
    Prop.to (Sat∂≈F p (F (Import φ))) sat∂'

  -- Derived: Export∘Import is satisfaction-equivalent to the identity on `Form`.

  Export∘Import≈F
    : ∀ p (φ : Form)
    → Prop._↔_ (SatF p φ) (SatF p (Interp (Import φ)))
  Export∘Import≈F p φ = Prop.↔-trans (SatF≈∂ p φ) (Sat∂≈F p (Import φ))

  -- Derived: if two formulas are indistinguishable by `SatF`, then their imports
  -- are indistinguishable by boundary satisfaction (`Sat∂`).

  Import-respects-ObsEqF
    : ∀ {φ ψ}
    → (∀ p → Prop._↔_ (SatF p φ) (SatF p ψ))
    → Import φ ≈∂[ B ] Import ψ
  Import-respects-ObsEqF {φ} {ψ} eq p =
    Prop.↔-trans
      (Prop.↔-sym (SatF≈∂ p φ))
      (Prop.↔-trans (eq p) (SatF≈∂ p ψ))

  -- Derived: Import∘Export is observationally the identity on boundary constraints.

  Import∘Export≈∂
    : ∀ p (c : Con_bnd)
    → Prop._↔_ (BoundaryIO.Sat∂ B p c)
               (BoundaryIO.Sat∂ B p (Import (Interp c)))
  Import∘Export≈∂ p c = Prop.↔-trans (Sat∂≈F p c) (SatF≈∂ p (Interp c))

-- Canonical port: take `Form = Con_bnd` and interpret by identity.

canonicalPort
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
  → BoundaryPort {ℓForm = ℓ} Sig Q W BB H B
canonicalPort {BB = BB} B =
  let open BulkBoundary BB in
  record
    { Sem = record
        { Form = Con_bnd
        ; SatF = λ p c → BoundaryIO.Sat∂ B p c
        ; Interp = λ c → c
        ; Sat∂≈F = λ _ _ → Prop.↔-refl
        }
    ; Import = λ φ → φ
    ; SatF≈∂ = λ _ _ → Prop.↔-refl
    }
