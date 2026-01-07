{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.TruthLemma where

-- “Truth lemma” in the LogOS sense:
-- truth at the S-tier is exactly truth at the H-tier of the translated constraint,
-- and H-tier truth is exactly boundary satisfaction (via `sat-coh`).
--
-- This is not a completeness theorem for a proof system; it is the internal
-- coherence principle that makes the three tiers denote the same semantics.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)

open import LogOS.Kernel
open import LogOS.Kernel.LogicKernel as LK

module KernelTruthLemma
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
  module ST = Truth.StrictTruth Sig

  -- S ↔ H (via `coh-LH`)
  S↔H
    : ∀ (w : LogOSSignature.Cosp Sig) (φ : Kernel.Fml K)
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w φ
      ↔ HT.HLayer.Sat_H (Kernel.HTruth K) w (Kernel.TransH K φ)
  S↔H w φ = Kernel.coh-LH K w φ

  -- H ↔ ∂ (via `sat-coh`)
  H↔∂
    : ∀ (w : LogOSSignature.Cosp Sig)
        (c : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
    → HT.HLayer.Sat_H (Kernel.HTruth K) w c
      ↔ Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
  H↔∂ w c = Kernel.sat-coh K w c

  -- S ↔ ∂ (derived)
  S↔∂
    : ∀ (w : LogOSSignature.Cosp Sig) (φ : Kernel.Fml K)
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w φ
      ↔ Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.TransH K φ)
  S↔∂ w φ =
    record
      { to   = λ satS → Prop._↔_.to (H↔∂ w (Kernel.TransH K φ)) (Prop._↔_.to (S↔H w φ) satS)
      ; from = λ sat∂ → Prop._↔_.from (S↔H w φ) (Prop._↔_.from (H↔∂ w (Kernel.TransH K φ)) sat∂)
      }

module LogicKernelTruthLemma
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.LogicKernel Sig Q)
  where

  open LK.LogicKernel K

  -- Operational step semantics matches boundary flow at the decoded level.
  Guard↔Step
    : ∀ (γ : Code)
    → decode (Guard γ) ≡ LK.GTier.Flow G (LK.GTier.step G) (decode γ)
  Guard↔Step = LK.LogicKernel.guard-decode K

  -- Distinguished code witness is exactly the G-tier fixed point at decode level.
  γ*↔Th*
    : decode γ* ≡ LK.GTier.Th* G
  γ*↔Th* = LK.LogicKernel.decode-γ* K
