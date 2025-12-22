{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Full where

open import LogOS.Prelude
open import Data.Product using (Σ; _,_)
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Algebra.ConAlg using (ConAlgHom≡)
import LogOS.Theorems.Meta.Assumptions.Core as A
open import LogOS.Kernel.Initial
open import LogOS.Theorems.Meta.Base using (NonTrivialC; DeciderC; mkDeciderC)
-- Use shared assumption packs

-- Canonical (initial) kernel helper interface

WorldH
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  → Set (lsuc ℓ)
WorldH Sig Q = Worlds.WorldH Sig Q

-- Canonical (initial) kernel derived from (Sig,Q) and a chosen world
FreeKernel
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    → WorldH Sig Q → Kernel Sig Q
FreeKernel Sig Q HW = InitialKernel.FreeK (build Sig Q HW)

foldTo
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    → (HW : WorldH Sig Q)
    → (K : Kernel Sig Q) → KernelHom (FreeKernel Sig Q HW) K
foldTo Sig Q HW K = InitialKernel.foldK (build Sig Q HW) K

-- Pullback of decidability along a Kernel hom (textbook: reductions preserve decidability).

decider-pullback
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    (P : Kernel.Code K₂ → Set ℓ)
  → DeciderC {K = K₂} P
  → DeciderC {K = K₁} (λ γ → P (KernelHom.mapCode h γ))
decider-pullback h P dec =
  mkDeciderC
    record
      { decide = λ γ → DeciderC.decide dec (KernelHom.mapCode h γ)
      ; total  = λ γ → DeciderC.total  dec (KernelHom.mapCode h γ)
      ; sound  = λ γ → DeciderC.sound  dec (KernelHom.mapCode h γ)
      ; comp   = λ γ → DeciderC.comp   dec (KernelHom.mapCode h γ)
      }

-- Contrapositive reduction lemma (textbook):
-- if P is undecidable on K₂, it is also undecidable on any domain that reduces to K₂.

noDecider-by-pullback
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    (P : Kernel.Code K₂ → Set ℓ)
  → ¬ (DeciderC {K = K₁} (λ γ → P (KernelHom.mapCode h γ)))
  → ¬ (DeciderC {K = K₂} P)
noDecider-by-pullback h P noDec dec =
  noDec (decider-pullback h P dec)

-- Reduction of decode-extensional properties along fold (FreeK → K)

decodeExt-pull
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (HW : WorldH Sig Q)
    (K : Kernel Sig Q)
    (P : Kernel.Code K → Set ℓ)
    → A.DecodeExtensional K P
    → A.DecodeExtensional (FreeKernel Sig Q HW) (λ γ → P (KernelHom.mapCode (foldTo Sig Q HW K) γ))
decodeExt-pull HW K P ext γ₁ γ₂ pr p =
  let open KernelHom (foldTo _ _ HW K) in
  ext _ _ (trans (map-decode γ₁)
        (trans (cong (ConAlgHom≡.map∂ con-hom) pr)
               (sym (map-decode γ₂)))) p

-- Transport undecidability from the canonical FreeKernel to any target kernel via fold.
-- (Textbook contrapositive: if P is decidable on K, then its pullback along fold is
-- decidable on FreeKernel.)

noDecider-transport
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (HW : WorldH Sig Q)
    (K : Kernel Sig Q)
    (P : Kernel.Code K → Set ℓ)
    (freeNoDecider
      : ¬ (DeciderC {K = FreeKernel Sig Q HW}
           (λ γ → P (KernelHom.mapCode (foldTo Sig Q HW K) γ))))
  → ¬ (DeciderC {K = K} P)
noDecider-transport HW K P freeNoDecider =
  noDecider-by-pullback (foldTo _ _ HW K) P freeNoDecider

-- Helper: build a mapped nontriviality for (λ γ → P (mapCode h γ)) from two witnesses.

nonTrivial-mapped
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (HW : WorldH Sig Q)
    (K  : Kernel Sig Q)
    (P  : Kernel.Code K → Set ℓ)
    (h  : KernelHom (FreeKernel Sig Q HW) K)
    (γT : Kernel.Code (FreeKernel Sig Q HW))
    (pT : P (KernelHom.mapCode h γT))
    (γF : Kernel.Code (FreeKernel Sig Q HW))
    (nF : ¬ (P (KernelHom.mapCode h γF)))
  → NonTrivialC {K = FreeKernel Sig Q HW} (λ γ → P (KernelHom.mapCode h γ))
nonTrivial-mapped HW K P h γT pT γF nF = (γT , pT) , (γF , nF)
