{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.ExtensionalReflection where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Fibrewise reflective strictification of extensional logic.
--
-- This theorem is intentionally relative:
-- extensional collapse is reflective only inside fibres that already carry
-- explicit classical-limit evidence (antisymmetry of the target boundary).
--
-- For any displayed doctrine `D` over `LOG`, we compare:
-- - observation-first `D`-logics with explicit classical-limit evidence, and
-- - the corresponding extensional `D`-logics, where strict decode is added.
--
-- The reflector derives the strict decode law from the classical-limit witness.
-- The inclusion forgets that extra strict decode witness.
-- Homwise, these form a Galois connection, because total refinement depends
-- only on the underlying `KernelHom` and ignores displayed evidence.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; MonoMap; _⊑_)
open import LogOS.LT.ConPreorder.Antisymmetry using (Antisymmetry)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Hom.Core as Hom using (KernelHom; decode-mapCode)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; ProductDisplayed
  ; DecoratedThin2Cat
  ; DecoratedObj
  ; DecoratedHom
  ; TotalHomPreorder
  ; mkTotalHomR
  ; baseHom
  ; disp
  ; dispHom
  ; mapDecorated
  )

import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.LOG.ClassicalLimit2Cat as ClassicalLimit
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode
import LogOS.LT.Theorems.AbstractGaloisConnection as Galois

ObservationFirstDisplayed
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
  → (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  → DisplayedThin2Cat
      (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode})
      (lsuc (ℓ ⊔ ℓRel) ⊔ ℓDObj)
      ℓDHom
ObservationFirstDisplayed {ℓ} {ℓRel} {ℓCode} D =
  ProductDisplayed (ClassicalLimit.ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode}) D

ExtensionalDisplayed
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
  → (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  → DisplayedThin2Cat
      (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode})
      (lsuc (ℓ ⊔ ℓRel) ⊔ ℓDObj)
      ((ℓ ⊔ ℓCode) ⊔ ℓDHom)
ExtensionalDisplayed {ℓ} {ℓRel} {ℓCode} D =
  ProductDisplayed
    (ClassicalLimit.ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode})
    (ProductDisplayed (StrictDecode.Displayed {ℓ} {ℓRel} {ℓCode}) D)

ObservationFirstFiber
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
  → (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel) ⊔ lsuc (ℓ ⊔ ℓRel ⊔ ℓCode) ⊔ ℓDObj)
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓDHom)
      (ℓRel ⊔ ℓCode)
ObservationFirstFiber D = DecoratedThin2Cat (ObservationFirstDisplayed D)

ExtensionalFiber
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
  → (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel) ⊔ lsuc (ℓ ⊔ ℓRel ⊔ ℓCode) ⊔ ℓDObj)
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ((ℓ ⊔ ℓCode) ⊔ ℓDHom))
      (ℓRel ⊔ ℓCode)
ExtensionalFiber D = DecoratedThin2Cat (ExtensionalDisplayed D)

includeExtensional
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
  → Thin2Functor
      (ExtensionalFiber D)
      (ObservationFirstFiber D)
includeExtensional {ℓ} {ℓRel} {ℓCode} {D = D} =
  mapDecorated
    (ExtensionalDisplayed {ℓ} {ℓRel} {ℓCode} D)
    (ObservationFirstDisplayed {ℓ} {ℓRel} {ℓCode} D)
    (λ {A} (anti , (_ , portA)) → anti , portA)
    (λ {A} {B} {f} {x} {y} (_ , (_ , compat)) → tt , compat)

strictifyFiber
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
  → Thin2Functor
      (ObservationFirstFiber D)
      (ExtensionalFiber D)
strictifyFiber {ℓ} {ℓRel} {ℓCode} {D = D} =
  mapDecorated
    (ObservationFirstDisplayed {ℓ} {ℓRel} {ℓCode} D)
    (ExtensionalDisplayed {ℓ} {ℓRel} {ℓCode} D)
    (λ {A} (anti , portA) → anti , (StrictDecode.strictDecodeUnit , portA))
    (λ {A} {B} {f} {x} {y} (_ , compat) →
      ( tt
      , ( (λ γ → Antisymmetry.antisym (fst y) (fst (decode-mapCode f γ)) (snd (decode-mapCode f γ)))
        , compat
        )
      ))

ObservationObj
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
  → (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  → Set _
ObservationObj D = Thin2Cat.Obj (ObservationFirstFiber D)

ExtensionalObj
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
  → (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  → Set _
ExtensionalObj D = Thin2Cat.Obj (ExtensionalFiber D)

ObservationHomPreorder
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
    (X : ObservationObj D)
    (Y : ExtensionalObj D)
  → ConPreorder _ (ℓRel ⊔ ℓCode)
ObservationHomPreorder D X Y =
  Thin2Cat.Hom (ObservationFirstFiber D) X (Thin2Functor.mapObj (includeExtensional {D = D}) Y)

ExtensionalHomPreorder
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
    (X : ObservationObj D)
    (Y : ExtensionalObj D)
  → ConPreorder _ (ℓRel ⊔ ℓCode)
ExtensionalHomPreorder D X Y =
  Thin2Cat.Hom (ExtensionalFiber D) (Thin2Functor.mapObj (strictifyFiber {D = D}) X) Y

forgetStrictDecodeHom
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
    {X : ObservationObj D}
    {Y : ExtensionalObj D}
  → Con (ExtensionalHomPreorder D X Y)
  → Con (ObservationHomPreorder D X Y)
forgetStrictDecodeHom h =
  mkTotalHomR
    (baseHom h)
    (tt , snd (snd (dispHom h)))

strictifyHom
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
    {X : ObservationObj D}
    {Y : ExtensionalObj D}
  → Con (ObservationHomPreorder D X Y)
  → Con (ExtensionalHomPreorder D X Y)
strictifyHom {Y = Y} h =
  mkTotalHomR
    (baseHom h)
    ( tt
    , ( (λ γ →
            Antisymmetry.antisym
              (fst (disp Y))
              (fst (decode-mapCode (baseHom h) γ))
              (snd (decode-mapCode (baseHom h) γ)))
      , snd (dispHom h)
      )
    )

strictifyHom-mono
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
    {X : ObservationObj D}
    {Y : ExtensionalObj D}
  → MonoMap
      (ObservationHomPreorder D X Y)
      (ExtensionalHomPreorder D X Y)
      (strictifyHom {D = D} {X = X} {Y = Y})
strictifyHom-mono le = le

forgetStrictDecodeHom-mono
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
    {X : ObservationObj D}
    {Y : ExtensionalObj D}
  → MonoMap
      (ExtensionalHomPreorder D X Y)
      (ObservationHomPreorder D X Y)
      (forgetStrictDecodeHom {D = D} {X = X} {Y = Y})
forgetStrictDecodeHom-mono le = le

homwiseAdjunction
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
    {X : ObservationObj D}
    {Y : ExtensionalObj D}
    (a : Con (ObservationHomPreorder D X Y))
    (b : Con (ExtensionalHomPreorder D X Y))
  → _⊑_ (ExtensionalHomPreorder D X Y)
      (strictifyHom {D = D} {X = X} {Y = Y} a)
      b
    ↔
    _⊑_ (ObservationHomPreorder D X Y)
      a
      (forgetStrictDecodeHom {D = D} {X = X} {Y = Y} b)
homwiseAdjunction _ _ =
  intro (λ le → le) (λ le → le)

homwiseExtensionalReflection
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
    (X : ObservationObj D)
    (Y : ExtensionalObj D)
  → Galois.GaloisConnection
      (ObservationHomPreorder D X Y)
      (ExtensionalHomPreorder D X Y)
homwiseExtensionalReflection {D = D} X Y =
  record
    { L = strictifyHom {D = D} {X = X} {Y = Y}
    ; R = forgetStrictDecodeHom {D = D} {X = X} {Y = Y}
    ; L-mono = λ le → le
    ; R-mono = λ le → le
    ; adj = λ _ _ → intro (λ le → le) (λ le → le)
    }

record FiberwiseExtensionalReflection
  {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
  (D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  : Setω where
  field
    include
      : Thin2Functor
          (ExtensionalFiber D)
          (ObservationFirstFiber D)

    reflect
      : Thin2Functor
          (ObservationFirstFiber D)
          (ExtensionalFiber D)

    homReflection
      : ∀ (X : ObservationObj D) (Y : ExtensionalObj D)
      → Galois.GaloisConnection
          (ObservationHomPreorder D X Y)
          (ExtensionalHomPreorder D X Y)

  reflectionUnit
    : ∀ (X : ObservationObj D) (Y : ExtensionalObj D)
    → ∀ h
    → _⊑_ (ObservationHomPreorder D X Y)
        h
        (Galois.R (homReflection X Y) (Galois.L (homReflection X Y) h))
  reflectionUnit X Y = Galois.unit (homReflection X Y)

  reflectionCounit
    : ∀ (X : ObservationObj D) (Y : ExtensionalObj D)
    → ∀ h
    → _⊑_ (ExtensionalHomPreorder D X Y)
        (Galois.L (homReflection X Y) (Galois.R (homReflection X Y) h))
        h
  reflectionCounit X Y = Galois.counit (homReflection X Y)

fiberwiseExtensionalReflection
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
  → FiberwiseExtensionalReflection D
fiberwiseExtensionalReflection {D = D} =
  record
    { include = includeExtensional {D = D}
    ; reflect = strictifyFiber {D = D}
    ; homReflection = homwiseExtensionalReflection {D = D}
    }
