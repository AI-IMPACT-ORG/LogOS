{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.Interoperability where

-- Port-level interoperability: adapters compose and are uniquely determined
-- (up to satisfaction) by the shared boundary semantics.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port
import LogOS.Ports.Semantic.Interlingua as Interlingua
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero
open import LogOS.Ports.Semantic.PresentationCore using
  ( PresentationC
  ; PresentationHom
  ; PresentationHom-respects-ObsEq
  )
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.InterlinguaStrictReindex as StrictReindex
open import LogOS.Adapters.Views.SatMor using (satMor-reindexKernel-strict)
open import LogOS.Kernel

record PortAdapter
  {ℓ : Level}
  {ℓForm₁ ℓForm₂ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  : Set (lsuc (ℓ ⊔ ℓForm₁ ⊔ ℓForm₂)) where
  private
    module P1 = BoundaryPort P₁
    module P2 = BoundaryPort P₂
  field
    map : P1.Form → P2.Form
    preserves-Sat : ∀ p φ → Prop._↔_ (P1.SatF p φ) (P2.SatF p (map φ))

open PortAdapter public

toPresentationHom
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
  → PortAdapter B P₁ P₂
  → PresentationHom (Interlingua.toPresentationC B P₁) (Interlingua.toPresentationC B P₂)
toPresentationHom B A =
  record
    { map = map A
    ; sem = preserves-Sat A
    }

fromPresentationHom
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
  → PresentationHom (Interlingua.toPresentationC B P₁) (Interlingua.toPresentationC B P₂)
  → PortAdapter B P₁ P₂
fromPresentationHom _ h =
  record
    { map = PresentationHom.map h
    ; preserves-Sat = PresentationHom.sem h
    }

adapter-respects-ObsEqF
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
  → (A : PortAdapter B P₁ P₂)
  → ∀ {φ ψ}
  → PresentationC.ObsEqF (Interlingua.toPresentationC B P₁) φ ψ
  → PresentationC.ObsEqF (Interlingua.toPresentationC B P₂) (map A φ) (map A ψ)
adapter-respects-ObsEqF B A =
  PresentationHom-respects-ObsEq (toPresentationHom B A)

idAdapter
  : ∀ {ℓ : Level}
    {ℓForm : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  → PortAdapter B P P
idAdapter _ _ =
  record
    { map = λ φ → φ
    ; preserves-Sat = λ _ _ → Prop.↔-refl
    }

composeAdapter
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
  → PortAdapter B P₁ P₂
  → PortAdapter B P₂ P₃
  → PortAdapter B P₁ P₃
composeAdapter _ _ _ _ A B =
  record
    { map = λ φ → map B (map A φ)
    ; preserves-Sat = λ p φ →
        Prop.↔-trans
          (preserves-Sat A p φ)
          (preserves-Sat B p (map A φ))
    }

composeAdapter-respects-ObsEqF
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ ℓForm₃ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
    {P₃ : BoundaryPort {ℓForm = ℓForm₃} Sig Q W BB H B}
  → (A : PortAdapter B P₁ P₂)
  → (B₁ : PortAdapter B P₂ P₃)
  → ∀ {φ ψ}
  → PresentationC.ObsEqF (Interlingua.toPresentationC B P₁) φ ψ
  → PresentationC.ObsEqF (Interlingua.toPresentationC B P₃)
      (map (composeAdapter B P₁ P₂ P₃ A B₁) φ)
      (map (composeAdapter B P₁ P₂ P₃ A B₁) ψ)
composeAdapter-respects-ObsEqF B A B₁ eq =
  adapter-respects-ObsEqF B B₁ (adapter-respects-ObsEqF B A eq)

module For
  {ℓ : Level}
  {ℓForm₁ ℓForm₂ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  where

  module I = Interlingua.For B P₁ P₂
  private
    module P2 = BoundaryPort P₂

  Adapter≈ : PortAdapter B P₁ P₂ → PortAdapter B P₁ P₂ → Set (ℓ ⊔ ℓForm₁)
  Adapter≈ A B = ∀ p φ → P2.SatF p (map A φ) ↔ P2.SatF p (map B φ)

  adapter≈-refl : ∀ (A : PortAdapter B P₁ P₂) → Adapter≈ A A
  adapter≈-refl _ _ _ = Prop.↔-refl

  adapter≈-sym
    : ∀ {A B : PortAdapter B P₁ P₂}
    → Adapter≈ A B
    → Adapter≈ B A
  adapter≈-sym ab p φ = Prop.↔-sym (ab p φ)

  adapter≈-trans
    : ∀ {A B C : PortAdapter B P₁ P₂}
    → Adapter≈ A B
    → Adapter≈ B C
    → Adapter≈ A C
  adapter≈-trans ab bc p φ = Prop.↔-trans (ab p φ) (bc p φ)

  canonicalAdapter : PortAdapter B P₁ P₂
  canonicalAdapter =
    record
      { map = I.translate
      ; preserves-Sat = I.translate-preserves-Sat
      }

  adapter-unique
    : ∀ (A : PortAdapter B P₁ P₂)
    → Adapter≈ A canonicalAdapter
  adapter-unique A = I.translate-unique (map A) (preserves-Sat A)

  -- Any two adapters between the same ports are observationally equivalent.
  adapter-confluent
    : ∀ {A A' : PortAdapter B P₁ P₂}
    → Adapter≈ A A'
  adapter-confluent {A} {A'} p φ =
    Prop.↔-trans
      (adapter-unique A p φ)
      (Prop.↔-sym (adapter-unique A' p φ))

from-to≈
  : ∀ {ℓ : Level}
    {ℓForm₁ ℓForm₂ : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    {P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B}
    {P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B}
  → (A : PortAdapter B P₁ P₂)
  → For.Adapter≈ B P₁ P₂ (fromPresentationHom B (toPresentationHom B A)) A
from-to≈ B A p φ = Prop.↔-refl

composeAdapter-cong
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
    {A A' : PortAdapter B P₁ P₂}
    {B₁ B₁' : PortAdapter B P₂ P₃}
  → For.Adapter≈ B P₁ P₂ A A'
  → For.Adapter≈ B P₂ P₃ B₁ B₁'
  → For.Adapter≈ B P₁ P₃
      (composeAdapter B P₁ P₂ P₃ A B₁)
      (composeAdapter B P₁ P₂ P₃ A' B₁')
composeAdapter-cong B P₁ P₂ P₃ {A} {A'} {B₁} {B₁'} eqA eqB p φ =
  let
    stepB : BoundaryPort.SatF P₃ p (map B₁ (map A φ))
              ↔ BoundaryPort.SatF P₃ p (map B₁' (map A φ))
    stepB = eqB p (map A φ)

    stepA : BoundaryPort.SatF P₃ p (map B₁' (map A φ))
              ↔ BoundaryPort.SatF P₃ p (map B₁' (map A' φ))
    stepA =
      Prop.↔-trans
        (Prop.↔-sym (preserves-Sat B₁' p (map A φ)))
        (Prop.↔-trans (eqA p φ) (preserves-Sat B₁' p (map A' φ)))
  in
  Prop.↔-trans stepB stepA

canonicalAdapter≈id
  : ∀ {ℓ : Level}
    {ℓForm : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q}
    {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (P : BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B)
  → For.Adapter≈ B P P (For.canonicalAdapter B P P) (idAdapter B P)
canonicalAdapter≈id B P p φ = Interlingua.translate-id B P p φ

canonicalAdapter≈comp
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
  → For.Adapter≈ B P₁ P₃
      (For.canonicalAdapter B P₁ P₃)
      (composeAdapter B P₁ P₂ P₃
        (For.canonicalAdapter B P₁ P₂)
        (For.canonicalAdapter B P₂ P₃))
canonicalAdapter≈comp B P₁ P₂ P₃ p φ =
  Interlingua.translate-comp B P₁ P₂ P₃ p φ

-- ---------------------------------------------------------------------------
-- Heterogeneous interlingua: canonical adapter across changing satisfactions.
-- ---------------------------------------------------------------------------

record HeteroPortAdapter
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {Ctx₁ : Set ℓCtx₁} {Con₁ : Set ℓCon₁} {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
  {Ctx₂ : Set ℓCtx₂} {Con₂ : Set ℓCon₂} {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
  (m  : SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ Con₂ Sat₂)
  : Set (lsuc (ℓCtx₁ ⊔ ℓCon₁ ⊔ ℓSat₁ ⊔ ℓForm₁ ⊔ ℓCtx₂ ⊔ ℓCon₂ ⊔ ℓSat₂ ⊔ ℓForm₂)) where
  private
    module H = Hetero.For m P₁ P₂
  field
    map : PresentationC.Form P₁ → PresentationC.Form P₂
    preserves-Sat : H.SemPreserving map

open HeteroPortAdapter public

heteroCanonicalAdapter
  : ∀ {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
    {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
    {Ctx₁ : Set ℓCtx₁} {Con₁ : Set ℓCon₁} {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
    {Ctx₂ : Set ℓCtx₂} {Con₂ : Set ℓCon₂} {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
    (m  : SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
    (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
    (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ Con₂ Sat₂)
  → HeteroPortAdapter m P₁ P₂
heteroCanonicalAdapter m P₁ P₂ =
  let module H = Hetero.For m P₁ P₂ in
  record
    { map = H.translate
    ; preserves-Sat = H.translate-preserves-Sat
    }

heteroAdapter-unique
  : ∀ {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
    {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
    {Ctx₁ : Set ℓCtx₁} {Con₁ : Set ℓCon₁} {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
    {Ctx₂ : Set ℓCtx₂} {Con₂ : Set ℓCon₂} {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
    (m  : SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
    (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
    (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ Con₂ Sat₂)
    (A  : HeteroPortAdapter m P₁ P₂)
  → let module H = Hetero.For m P₁ P₂ in
    H._≈⇒_ (map A) H.translate
heteroAdapter-unique m P₁ P₂ A =
  let module H = Hetero.For m P₁ P₂ in
  H.translate-unique (map A) (preserves-Sat A)

strictReindexAdapter
  : ∀ {ℓ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → Kernel.Fml K)
  → let module SR = StrictReindex.ForKernel σ K mapFml
    in HeteroPortAdapter (satMor-reindexKernel-strict σ K mapFml) SR.P₁ SR.P₂
strictReindexAdapter σ K mapFml =
  let module SR = StrictReindex.ForKernel σ K mapFml in
  heteroCanonicalAdapter (satMor-reindexKernel-strict σ K mapFml) SR.P₁ SR.P₂
