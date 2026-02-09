{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

import LogOS.Minimal.RelPreorder as RP
import LogOS.Minimal.View as View

open import LogOS.Boundary.IO
open import LogOS.Boundary.Semantics

-- Boundary observational equality induced by a `BoundaryIO`.
--
-- Conventions:
-- - `c ≈∂[ B ] d` is *mutual refinement* in the observational preorder induced
--   by `BoundaryIO.Sat∂ B` (i.e. `ObsLeOn` both ways).
-- - `ObsEq∂ B c d` is the presentation form as pointwise propositional
--   equivalence (`ObsEqOn`, using `_↔_`).

infix 4 _≈∂[_]_
_≈∂[_]_ : ∀ {ℓ}
          {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
          {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
          {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
        → BulkBoundary.Con_bnd BB
        → BoundaryIO Sig Q W BB H
        → BulkBoundary.Con_bnd BB
        → Set ℓ
_≈∂[_]_ c B d = View.Obs≈ (BoundaryIO.Sat∂ B) c d

-- Non-glyph alias (keeps notation consistent with `Obs≈obs` in kernel tiers).
Obs≈∂ : ∀ {ℓ}
         {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
         {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
       → BoundaryIO Sig Q W BB H
       → BulkBoundary.Con_bnd BB
       → BulkBoundary.Con_bnd BB
       → Set ℓ
Obs≈∂ B c d = c ≈∂[ B ] d

-- Presentation alias (cf. `LogOS.Computation.Scheme.ObsEq` / OS theorems).

ObsEq∂ : ∀ {ℓ}
         {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
         {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
       → BoundaryIO Sig Q W BB H
       → BulkBoundary.Con_bnd BB
       → BulkBoundary.Con_bnd BB
       → Set ℓ
ObsEq∂ B c d = Prop.ObsEqOn (BoundaryIO.Sat∂ B) c d

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

-- Same observational target packaged in the two-level preorder interface
-- (`RelPreorder`), so it can be used uniformly as a view target.
ObsBndRelPreorder
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → RP.RelPreorder ℓ ℓ
ObsBndRelPreorder {BB = BB} B =
  View.ObsPreorder (BoundaryIO.Sat∂ B)

Respects≈∂[_] : ∀ {ℓ}
                {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
                {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
              → (B : BoundaryIO Sig Q W BB H)
              → (BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB)
              → Set ℓ
Respects≈∂[ B ] F = ∀ {c d} → c ≈∂[ B ] d → F c ≈∂[ B ] F d

RespectsObsEqBnd
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → (BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB)
  → Set ℓ
RespectsObsEqBnd B F = ∀ {c d} → ObsEq∂ B c d → ObsEq∂ B (F c) (F d)

-- Canonical form: extensionality w.r.t. boundary observational mutual refinement.
RespectsObs≈Bnd
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → (BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB)
  → Set ℓ
RespectsObs≈Bnd = Respects≈∂[_]

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
≈∂-refl B c = RP.≈RP-refl (ObsBndRelPreorder B) c

≈∂-sym
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → {B : BoundaryIO Sig Q W BB H}
  → {c d : BulkBoundary.Con_bnd BB}
  → c ≈∂[ B ] d
  → d ≈∂[ B ] c
≈∂-sym {B = B} = RP.≈RP-sym {RP = ObsBndRelPreorder B}

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
≈∂-trans {B = B} = RP.≈RP-trans {RP = ObsBndRelPreorder B}

ObsEq∂↔≈∂
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → {c d : BulkBoundary.Con_bnd BB}
  → Prop._↔_
      (ObsEq∂ B c d)
      (c ≈∂[ B ] d)
ObsEq∂↔≈∂ B {c} {d} =
  Prop.ObsEqOn↔ObsLeOn {Sat = BoundaryIO.Sat∂ B} {x = c} {y = d}

ObsEq∂↔Obs≈∂
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → {c d : BulkBoundary.Con_bnd BB}
  → Prop._↔_ (ObsEq∂ B c d) (Obs≈∂ B c d)
ObsEq∂↔Obs≈∂ B = ObsEq∂↔≈∂ B

RespectsObsEqBnd↔Respects≈∂
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → {F : BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB}
  → Prop._↔_ (RespectsObsEqBnd B F) (Respects≈∂[ B ] F)
RespectsObsEqBnd↔Respects≈∂ B {F} =
  Prop.intro
    (λ ext {c} {d} cd≈ →
      Prop._↔_.to (ObsEq∂↔Obs≈∂ B {c = F c} {d = F d})
        (ext (Prop._↔_.from (ObsEq∂↔Obs≈∂ B {c = c} {d = d}) cd≈)))
    (λ ext {c} {d} cdEq →
      Prop._↔_.from (ObsEq∂↔Obs≈∂ B {c = F c} {d = F d})
        (ext (Prop._↔_.to (ObsEq∂↔Obs≈∂ B {c = c} {d = d}) cdEq)))

mono-ObsBnd-respects≈∂
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → {B : BoundaryIO Sig Q W BB H}
  → {F : BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB}
  → MonoOn (ObsBndPreorder B) F
  → Respects≈∂[ B ] F
mono-ObsBnd-respects≈∂ {B = B} monoF =
  monoOn-respects≈ {CP = ObsBndPreorder B} monoF

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
  Import-respects-ObsEqF {φ} {ψ} eq =
    ( (λ p sat∂φ →
        Prop.to (SatF≈∂ p ψ)
          (Prop.to (eq p) (Prop.from (SatF≈∂ p φ) sat∂φ)))
    , (λ p sat∂ψ →
        Prop.to (SatF≈∂ p φ)
          (Prop.from (eq p) (Prop.from (SatF≈∂ p ψ) sat∂ψ)))
    )

  -- Canonical alias: accept mutual refinement (`Obs≈`) as the input notion.
  Import-respects-Obs≈F
    : ∀ {φ ψ}
    → View.Obs≈ SatF φ ψ
    → Import φ ≈∂[ B ] Import ψ
  Import-respects-Obs≈F {φ} {ψ} eq≈ =
    Import-respects-ObsEqF
      (Prop._↔_.from (View.ObsEqOn↔Obs≈ SatF {x = φ} {y = ψ}) eq≈)

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
