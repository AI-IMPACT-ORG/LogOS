{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.ProofTheory where

-- Proof-theory view: provability is refinement from the distinguished truth code.
-- This is a kernel-native, minimal sequent-style presentation.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
import LogOS.Minimal.Con.Rewrite as ConRewrite

open import LogOS.Kernel
import LogOS.Theorems.Meta.Assumptions.Core as Assump
open import LogOS.Theorems.Meta.Base using (NonTrivialC)
import LogOS.Theorems.Meta.CHL.Core as CHL

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module C = CHL.For K
  open C

  private
    CP = BulkBoundary.bnd (Kernel.BB K)
    module R = ConRewrite.For CP

  -- “Provability”: refinement from the distinguished truth code.
  Prov : Ty → Set ℓ
  Prov φ = Refines truth φ

  prov-refl : Prov truth
  prov-refl = refl-refines

  prov-cut : ∀ {φ ψ} → Prov φ → Refines φ ψ → Prov ψ
  prov-cut = cut-refines

  -- FlowCode (Box) preserves provability using the guarded fixed point.
  prov-box : ∀ {φ} → Prov φ → Prov (Box φ)
  prov-box {φ} pr =
    let
      step₁ = truth≤Box
      step₂ = box-mono pr
    in cut-refines step₁ step₂

  -- Decode-extensionality for provability.
  prov-ext : Assump.DecodeExtensional K Prov
  prov-ext _ _ eq le = R.substR eq le

  mkProvability : NonTrivialC {K = K} Prov → Assump.Provability K
  mkProvability nt =
    record
      { Prov    = Prov
      ; ext     = prov-ext
      ; nontriv = nt
      }

  -- ProvabilityOps with Box fixed to FlowCode, Imp left as a parameter.
  mkOps
    : (Imp : Ty → Ty → Ty)
    → Assump.ProvabilityOps K
  mkOps Imp =
    record
      { Imp = Imp
      ; Box = Box
      }

  -- Minimal Hilbert-style system for the CHL provability predicate.
  -- Imp is provided externally; Box is fixed to FlowCode.

  record Hilbert : Set (lsuc ℓ) where
    field
      Imp     : Ty → Ty → Ty
      prov    : Assump.Provability K
      ops     : Assump.ProvabilityOps K
      impRule : Assump.ImpRules K prov ops

  hilbert-from
    : (Imp : Ty → Ty → Ty)
    → (nt : NonTrivialC {K = K} Prov)
    → Assump.ImpRules K (mkProvability nt) (mkOps Imp)
    → Hilbert
  hilbert-from Imp nt rules =
    record
      { Imp     = Imp
      ; prov    = mkProvability nt
      ; ops     = mkOps Imp
      ; impRule = rules
      }

  -- Modal rules induced by FlowCode on provability.
  record ModalRules : Set (lsuc ℓ) where
    field
      Necessitation : ∀ {φ} → Prov φ → Prov (Box φ)
      Four          : ∀ {φ} → Prov (Box φ) → Prov (Box (Box φ))

  modalRules : ModalRules
  modalRules =
    record
      { Necessitation = prov-box
      ; Four          = prov-box
      }
