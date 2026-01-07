{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.RiceTransport where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥; ¬_)
open import Data.Product using (Σ; _,_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.Initial

open import LogOS.Domain.Universality.Core as U
open import LogOS.Domain.Universality.KernelRich
open import LogOS.Domain.Universality.Lemmas as UL

open import LogOS.Theorems.Meta.Assumptions.Core as A
open import LogOS.Theorems.Meta.Full as F
open import LogOS.Theorems.Meta.Base using (NonTrivialC; DeciderC)
open import LogOS.Prelude as Eq using (_≡_; refl; sym; subst)

-- Target kernel: universality code with identity decode.
-- This example shows how to transport a Rice-style undecidability claim for a
-- nontrivial decode-extensional property on the universality kernel, assuming
-- a local FreeKernel Rice proof for the mapped property.
K : Kernel Sig Q
K = UKR

-- Property on ToyUCode: “is in the ToyT branch” (nontrivial)
P : Kernel.Code K → Set lzero
P (U.ToyT _) = ⊤
{-# CATCHALL #-}
P _        = ⊥

-- Decode-extensionality on K (decode = id)
extK : A.DecodeExtensional K P
extK γ₁ γ₂ pr p = subst (λ x → P x) pr p

-- Canonical FreeKernel and fold hom
FKU : Kernel Sig Q
FKU = UL.FK

hU : KernelHom FKU K
hU = UL.h

-- Mapped non-triviality at FreeKernel via two specific codes
-- Pick the actual constructors from Free.Constraints
open import LogOS.Free.Constraints as FreeC

dT : Kernel.Code FKU
dT = FreeC.I∂

dF : Kernel.Code FKU
dF = FreeC.bnd FreeC.Ib

-- Concrete reduction lemmas (definitional under KernelRich) are available in UL.

pT : P (KernelHom.mapCode hU dT)
pT = tt

nF : ¬ P (KernelHom.mapCode hU dF)
nF p with UL.eq-dF
... | refl = p

nonTrivMapped
  : NonTrivialC {K = FKU} (λ γ → P (KernelHom.mapCode hU γ))
nonTrivMapped = (dT , pT) , (dF , nF)

-- FreeKernel undecidability for the mapped property is an input assumption.
record RiceAssumptionsU : Set₁ where
  field
    freeNoDecider
      : ¬ (DeciderC {K = FKU} (λ γ → P (KernelHom.mapCode hU γ)))

-- From these, derive undecidability of P on the universality kernel K

noDeciderP : (RA : RiceAssumptionsU) → ¬ (DeciderC {K = K} P)
noDeciderP RA =
  F.noDecider-transport HWorld K P (RiceAssumptionsU.freeNoDecider RA)
