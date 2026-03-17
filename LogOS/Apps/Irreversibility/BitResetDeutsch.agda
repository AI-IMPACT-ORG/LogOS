{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Irreversibility.BitResetDeutsch where

-- One-site physical semantics for the total reset example.
--
-- The reset itself is a locality/causality-respecting physical morphism, but
-- it cannot lift to the Deutsch stack because that stack already requires a
-- local reversibility witness. Landauer cost remains an explicit extra layer.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; MonoMap; _≈_; refl⊑)
open import LogOS.LT.Flow using (idClosure)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (mapHom)
open import LogOS.LT.DisplayedThin2Cat using (mkTotalObjR; mkTotalHomR; dispHom)

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
import LogOS.Ports.AbstractDeutsch2Cat as Deutsch2Cat

import LogOS.Apps.Irreversibility.BitReset as BitReset

BitPS : DependentLocalSemantics {lzero} {lzero} {lzero}
BitPS =
  record
    { I = ⊤
    ; O = λ _ → BitReset.BitPreorder
    ; GC₀ = λ _ → idClosure BitReset.BitPreorder
    }

open DependentLocalSemantics BitPS using (Bnd; I; O)

module D = Deutsch2Cat.Deutsch2CatLocal {lzero} {lzero} {lzero} {lzero} BitPS
module Loc = D.Locality
module Cau = D.Causality
module Rev = D.Reversibility
module Deutsch = D.Deutsch

BitPhysicalKernel : Loc.PhysicalKernel
BitPhysicalKernel =
  record
    { Code = BitReset.Bit
    ; decode = λ b _ → b
    }

bitLocalObj : Thin2Cat.Obj Loc.WithPort
bitLocalObj = Loc.physicalObj BitPhysicalKernel

bitCausalObj : Thin2Cat.Obj Cau.WithPort
bitCausalObj = mkTotalObjR bitLocalObj Cau.ttCausal

bitDeutschObj : Thin2Cat.Obj Deutsch.WithPort
bitDeutschObj = mkTotalObjR bitCausalObj Rev.ttReversible

resetAt : (i : I) → BitReset.Bit → BitReset.Bit
resetAt _ _ = BitReset.zero

resetMonoAt : ∀ i → MonoMap (O i) (O i) (resetAt i)
resetMonoAt _ = λ { refl → refl }

resetPhysical : Loc.PhysicalHom BitPhysicalKernel BitPhysicalKernel
resetPhysical =
  Loc.Strict.mkPhysicalHom≡
    resetAt
    resetMonoAt
    BitReset.resetBoundary
    (λ _ → refl)

resetPhysical-collapses-zero-one
  : _≈_ BitReset.BitPreorder
      (Loc.physicalMapAt resetPhysical tt BitReset.zero)
      (Loc.physicalMapAt resetPhysical tt BitReset.one)
resetPhysical-collapses-zero-one = (refl , refl)

resetCausal : Con (Thin2Cat.Hom Cau.WithPort bitCausalObj bitCausalObj)
resetCausal =
  mkTotalHomR
    resetPhysical
    (record
      { preserves-Flow = λ _ → refl⊑ Bnd
      })

resetPhysical-notLocalReversible : ¬ Rev.LocalReversible resetCausal
resetPhysical-notLocalReversible =
  Rev.collapse-obstructs-localReversible
    tt
    BitReset.zero
    BitReset.one
    BitReset.zero≉one
    resetPhysical-collapses-zero-one

resetCannotLiftToDeutsch
  : ¬ Σ
      (Con (Thin2Cat.Hom Deutsch.WithPort bitDeutschObj bitDeutschObj))
      (λ h → mapHom Deutsch.forget h ≡ resetCausal)
resetCannotLiftToDeutsch (h , eq) =
  resetPhysical-notLocalReversible
    (subst Rev.LocalReversible eq (dispHom h))
