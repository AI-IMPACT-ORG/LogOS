{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.BodyEqTransport where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥; ¬_)
open import LogOS.Prelude.Product using (Σ; _,_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Initial

open import LogOS.Domain.Universality.Core as U
open import LogOS.Domain.Universality.KernelRich
open import LogOS.Domain.Universality.Lemmas as UL

open import LogOS.Theorems.Meta.Full as F
open import LogOS.Theorems.Meta.Base using (NonTrivialC; DeciderC)
open import LogOS.Theorems.Meta.BodyEquivParam as BodyEq
open import LogOS.Prelude as Eq using (_≡_; refl; sym; subst)

-- Target kernel with decode = id on CoreUCode
K : Kernel Sig Q
K = UKR

-- Fix a concrete code δ
δ : Kernel.Code K
δ = U.CoreT (U.mkT 0 0)

-- Canonical FreeKernel and fold hom
FKU : Kernel Sig Q
FKU = UL.FK

hU : KernelHom FKU K
hU = UL.h

-- Nontriviality of Body∂-equivalence to δ on the mapped property at FreeK.
-- Since Body∂ is identity in this kernel, this reduces to plain code equality.
open import LogOS.Free.Constraints as FreeC

dT : Kernel.Code FKU
dT = FreeC.I∂

dF : Kernel.Code FKU
dF = FreeC.bnd FreeC.Ib

pT : BodyEq.BodyEqP K δ (KernelHom.mapCode hU dT)
pT = Eq.cong (Kernel.Body∂ K) (Eq.cong (Kernel.decode K) UL.eq-dT)

nF : ¬ (BodyEq.BodyEqP K δ (KernelHom.mapCode hU dF))
nF q with UL.eq-dF
... | refl with q
... | ()

nonTrivMapped
  : NonTrivialC {K = FKU} (λ γ → BodyEq.BodyEqP K δ (KernelHom.mapCode hU γ))
nonTrivMapped = (dT , pT) , (dF , nF)

-- FreeKernel undecidability for the mapped property is an input assumption.
record RiceAssumptionsBodyEq : Set₁ where
  field
    freeNoDecider
      : ¬ (DeciderC {K = FKU} (λ γ → BodyEq.BodyEqP K δ (KernelHom.mapCode hU γ)))

-- Undecidability of BodyEqP K δ on K by transport
noDecider-BodyEq : (RA : RiceAssumptionsBodyEq) → ¬ (DeciderC {K = K} (BodyEq.BodyEqP K δ))
noDecider-BodyEq RA =
  BodyEq.noDecider-BodyEq-transport HWorld K δ (RiceAssumptionsBodyEq.freeNoDecider RA)

-- Sanity lemma: the positive witness is definitional under KernelRich
pos-witness : BodyEq.BodyEqP K δ (KernelHom.mapCode hU dT)
pos-witness = pT
