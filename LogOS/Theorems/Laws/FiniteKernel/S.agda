{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Laws.FiniteKernel.S where

-- S-tier ↔ H-tier satisfaction transport inside a Kernel via the coherence
-- field. These are proven and require no postulates.

open import LogOS.Prelude
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Syntax.Prop as Prop

-- Transport S-tier strict satisfaction to H-tier via Kernel's coherence

S→H
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    → (w : (LogOSSignature.Cosp (Sig)))
    → (φ : Kernel.Fml K)
    → Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) w φ
    → (let module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K) in
       HT.HLayer.Sat_H (Kernel.HTruth K) w (Kernel.TransH K φ))
S→H Sig Q K w φ p =
  let open LogOSSignature Sig in
  let open Kernel K in
  Prop._↔_.to (coh-LH w φ) p

-- Transport H-tier satisfaction back to S-tier via Kernel's coherence

H→S
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    → (w : (LogOSSignature.Cosp (Sig)))
    → (φ : Kernel.Fml K)
    → (let module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K) in
       HT.HLayer.Sat_H (Kernel.HTruth K) w (Kernel.TransH K φ))
    → Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) w φ
H→S Sig Q K w φ q =
  let open LogOSSignature Sig in
  let open Kernel K in
  Prop._↔_.from (coh-LH w φ) q
