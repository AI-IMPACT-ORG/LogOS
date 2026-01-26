{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.Interlingua where

-- Canonical “glue” between external boundary presentations.
--
-- If two external systems are ports over the same LogOS boundary satisfaction,
-- then the meaning-preserving translation between them is forced (up to the
-- satisfaction-equivalence notion of equality).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port

import LogOS.Ports.Semantic.InterlinguaCore as Core

toPresentationC
  : ∀ {ℓ : Level}
    {ℓForm : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  → Core.PresentationC {ℓForm = ℓForm}
      (LogOSSignature.∂Cosp Sig) (BulkBoundary.Con_bnd BB) (BoundaryIO.Sat∂ B)
toPresentationC B P = record
  { Form   = BoundaryPort.Form P
  ; SatF   = BoundaryPort.SatF P
  ; Export = BoundaryPort.Interp P
  ; SatC≈F = BoundaryPort.Sat∂≈F P
  ; Import = BoundaryPort.Import P
  ; SatF≈C = BoundaryPort.SatF≈∂ P
  }

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  {W   : Worlds.WorldH Sig Q}
  {BB  : BulkBoundary ℓ}
  {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B   : BoundaryIO Sig Q W BB H)
  {ℓForm₁ ℓForm₂ : Level}
  (P₁  : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂  : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  where

  open LogOSSignature Sig
  open BulkBoundary BB

  private
    -- Port 1 interface
    module P1 = BoundaryPort P₁
    Form₁  = P1.Form
    SatF₁  = P1.SatF
    Interp₁ = P1.Interp
    Import₁ = P1.Import
    Sat∂≈F₁ = P1.Sat∂≈F
    SatF≈∂₁ = P1.SatF≈∂

    -- Port 2 interface
    module P2 = BoundaryPort P₂
    Form₂  = P2.Form
    SatF₂  = P2.SatF
    Interp₂ = P2.Interp
    Import₂ = P2.Import
    Sat∂≈F₂ = P2.Sat∂≈F
    SatF≈∂₂ = P2.SatF≈∂

    module C = Core.ForPresentations {SatC = BoundaryIO.Sat∂ B} (toPresentationC B P₁) (toPresentationC B P₂)

  -- Boundary observational equivalence (w.r.t. `Sat∂`).

  infix 4 _≈∂_
  _≈∂_ : Con_bnd → Con_bnd → Set ℓ
  c ≈∂ d = c ≈∂[ B ] d

  -- “Logic is well-defined on observations”: an endomap respects `≈∂`.

  Respects≈∂ : (Con_bnd → Con_bnd) → Set ℓ
  Respects≈∂ F = Respects≈∂[ B ] F

  -- The canonical translation (route through the shared boundary constraints).

  translate : Form₁ → Form₂
  translate = C.translate

  -- Meaning preservation is forced: translation is sound+complete by construction.

  translate-preserves-Sat
    : ∀ (p : ∂Cosp) (φ : Form₁)
    → Prop._↔_ (SatF₁ p φ) (SatF₂ p (translate φ))
  translate-preserves-Sat = C.translate-preserves-Sat

  -- Equality notion for translations: indistinguishable by satisfaction.

  infix 4 _≈⇒_
  _≈⇒_ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set (ℓ ⊔ ℓForm₁)
  t ≈⇒ u = C._≈⇒_ t u

  -- Named alias: satisfaction-equivalence on translations.
  Trans≈ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set (ℓ ⊔ ℓForm₁)
  Trans≈ = _≈⇒_

  -- A semantics-preserving translation is unique up to `≈⇒`.

  SemPreserving : (Form₁ → Form₂) → Set (ℓ ⊔ ℓForm₁)
  SemPreserving t = ∀ (p : ∂Cosp) (φ : Form₁) → Prop._↔_ (SatF₁ p φ) (SatF₂ p (t φ))

  translate-unique
    : ∀ (t : Form₁ → Form₂)
    → SemPreserving t
    → Trans≈ t translate
  translate-unique = C.translate-unique

  -- -------------------------------------------------------------------------
  -- Ported closure/normalisation: any boundary endomap lifts to every port.
  -- -------------------------------------------------------------------------

  Extend₁ : (Con_bnd → Con_bnd) → Form₁ → Form₁
  Extend₁ = P1.Extend

  Extend₂ : (Con_bnd → Con_bnd) → Form₂ → Form₂
  Extend₂ = P2.Extend

  -- If the boundary endomap is observationally extensional (respects `≈∂`),
  -- then the induced “Extend” operation commutes with the canonical translation.

  ported-closure-naturality
    : ∀ (F : Con_bnd → Con_bnd)
    → Respects≈∂ F
    → ∀ (p : ∂Cosp) (φ : Form₁)
    → Prop._↔_ (SatF₂ p (translate (Extend₁ F φ)))
               (SatF₂ p (Extend₂ F (translate φ)))
  ported-closure-naturality F extF p φ =
    C.ported-closure-naturality F extF p φ

  -- Alias (paper-friendly name).
  extend-commutes-with-translate = ported-closure-naturality

  ported-closure-naturality-ObsEndo
    : (endo : ObsEndo∂ B)
    → ∀ (p : ∂Cosp) (φ : Form₁)
    → Prop._↔_ (SatF₂ p (translate (Extend₁ (ObsEndo∂.fn endo) φ)))
               (SatF₂ p (Extend₂ (ObsEndo∂.fn endo) (translate φ)))
  ported-closure-naturality-ObsEndo endo p φ =
    ported-closure-naturality (ObsEndo∂.fn endo) (ObsEndo∂.respects endo) p φ

  -- Exported theories are presentation-independent (up to satisfaction).

  export-agrees-on-constraints
    : ∀ (p : ∂Cosp) (c : Con_bnd)
    → Prop._↔_ (SatF₁ p (Interp₁ c)) (SatF₂ p (Interp₂ c))
  export-agrees-on-constraints p c =
    let
      e₁ : Prop._↔_ (SatF₁ p (Interp₁ c)) (BoundaryIO.Sat∂ B p c)
      e₁ = Prop.↔-sym (Sat∂≈F₁ p c)
      e₂ : Prop._↔_ (BoundaryIO.Sat∂ B p c) (SatF₂ p (Interp₂ c))
      e₂ = Sat∂≈F₂ p c
    in Prop.↔-trans e₁ e₂

  export-agrees-on-Th⋆
    : ∀ (p : ∂Cosp) (Th⋆ : Con_bnd)
    → Prop._↔_ (SatF₁ p (Interp₁ Th⋆)) (SatF₂ p (Interp₂ Th⋆))
  export-agrees-on-Th⋆ = export-agrees-on-constraints

-- -----------------------------------------------------------------------------
-- Convenient top-level wrappers (avoid opening the parameterised module).
-- -----------------------------------------------------------------------------

translate
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  → BoundaryPort.Form P₁ → BoundaryPort.Form P₂
translate B P₁ P₂ = For.translate B P₁ P₂

translate-preserves-Sat
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  → ∀ (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P₁)
  → Prop._↔_ (BoundaryPort.SatF P₁ p φ)
             (BoundaryPort.SatF P₂ p (translate B P₁ P₂ φ))
translate-preserves-Sat B P₁ P₂ = For.translate-preserves-Sat B P₁ P₂

translate-id
  : ∀ {ℓ : Level}
    {ℓForm : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  → ∀ (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P)
  → Prop._↔_
      (BoundaryPort.SatF P p (translate B P P φ))
      (BoundaryPort.SatF P p φ)
translate-id B P p φ = Core.translate-id-core (toPresentationC B P) p φ

translate-unique
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
    (t : BoundaryPort.Form P₁ → BoundaryPort.Form P₂)
  → (∀ (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P₁)
     → Prop._↔_ (BoundaryPort.SatF P₁ p φ) (BoundaryPort.SatF P₂ p (t φ)))
  → (∀ (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P₁)
     → Prop._↔_ (BoundaryPort.SatF P₂ p (t φ))
                (BoundaryPort.SatF P₂ p (translate B P₁ P₂ φ)))
translate-unique B P₁ P₂ = For.translate-unique B P₁ P₂

translate-comp
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ ℓForm₃ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
    (P₃ : BoundaryPort {ℓForm = ℓForm₃} Sig Q W BB H B)
  → ∀ (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P₁)
  → Prop._↔_
      (BoundaryPort.SatF P₃ p (translate B P₁ P₃ φ))
      (BoundaryPort.SatF P₃ p (translate B P₂ P₃ (translate B P₁ P₂ φ)))
translate-comp B P₁ P₂ P₃ p φ =
  Core.translate-comp-core (toPresentationC B P₁) (toPresentationC B P₂) (toPresentationC B P₃) p φ

ported-closure-naturality
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
    (F : BulkBoundary.Con_bnd BB → BulkBoundary.Con_bnd BB)
  → Respects≈∂[ B ] F
  → ∀ (p : LogOSSignature.∂Cosp Sig) (φ : BoundaryPort.Form P₁)
  → Prop._↔_
      (BoundaryPort.SatF P₂ p (translate B P₁ P₂ (BoundaryPort.Extend P₁ F φ)))
      (BoundaryPort.SatF P₂ p (BoundaryPort.Extend P₂ F (translate B P₁ P₂ φ)))
ported-closure-naturality B P₁ P₂ = For.ported-closure-naturality B P₁ P₂

extend-commutes-with-translate = ported-closure-naturality

export-agrees-on-constraints
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  → ∀ (p : LogOSSignature.∂Cosp Sig) (c : BulkBoundary.Con_bnd BB)
  → Prop._↔_ (BoundaryPort.SatF P₁ p (BoundaryPort.Interp P₁ c))
             (BoundaryPort.SatF P₂ p (BoundaryPort.Interp P₂ c))
export-agrees-on-constraints B P₁ P₂ = For.export-agrees-on-constraints B P₁ P₂

export-agrees-on-Th⋆
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  → ∀ (p : LogOSSignature.∂Cosp Sig) (Th⋆ : BulkBoundary.Con_bnd BB)
  → Prop._↔_ (BoundaryPort.SatF P₁ p (BoundaryPort.Interp P₁ Th⋆))
             (BoundaryPort.SatF P₂ p (BoundaryPort.Interp P₂ Th⋆))
export-agrees-on-Th⋆ B P₁ P₂ = For.export-agrees-on-Th⋆ B P₁ P₂
