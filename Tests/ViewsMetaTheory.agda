{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.ViewsMetaTheory where

-- Coherence checks for the “one system, many views” narrative.
--
-- This is intentionally lightweight: it does not add axioms or collapse preorders.
-- It only checks that the bridge points between interfaces exist and compose.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom; composeSigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Kernel
open import LogOS.Kernel.Graded
open import LogOS.Kernel.LogicKernel
open import LogOS.Boundary.IO using (BoundaryIO)

import LogOS.Kernel.Hom2Cat as K2
import LogOS.Kernel.Graded.Hom2Cat as GK2
import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFromG
import LogOS.Kernel.LogicKernel.Hom2Cat as LK2
import LogOS.Kernel.Hom as KH
import LogOS.Kernel.Graded.Hom as GKH
import LogOS.Kernel.Reindex as Reindex
import LogOS.Kernel.HomOverSig as HomOverSig
import LogOS.Kernel.Boundary as KBoundary
import LogOS.Theorems.Meta.Views as Views
import LogOS.Theorems.Meta.TruthLemma as TruthLemma
import LogOS.Theorems.Meta.ObserverFromLogicKernel as ObsLK
import LogOS.Boundary.Port as Port
import LogOS.Ports.Semantic.Interlingua as Interlingua

-- The documentation view modules should be mutually importable.
open import docs.Views.CategoricalLogic
open import docs.Views.HoTT_3Level
open import docs.Views.MultiInstitution
open import docs.Views.ObserverSemantics
open import docs.Views.CurryHowardLambek
open import docs.Views.MeredithSentences

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where

  -- Kernel ↪ LogicKernel: the unified interface is available for every kernel.
  open Views.KernelIntoLogicKernel {ℓ} {Sig} {Q}
    renaming
      ( asLogicKernel to asLogicKernel-K
      ; toLKHom₁     to toLKHom₁-K
      ; fromLKHom₁   to fromLKHom₁-K
      ; to-from      to to-from-K
      ; from-to      to from-to-K
      )

  -- Underlying structural kernel hom is still available.
  underlyingKernelHom
    : ∀ {K₁ K₂ : Kernel Sig Q}
    → K2.KernelHom₁ K₁ K₂
    → KH.KernelHom K₁ K₂
  underlyingKernelHom = K2.homKernel

  -- Graded kernels also embed into the unified interface.
  asLogicKernel-G : GradedKernel Sig Q → LogicKernel Sig Q
  asLogicKernel-G = LKFromG.asLogicKernel

  -- Reindexing + heterogeneous morphism coherence exists at kernel level.
  module _ {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ}
           (σ : SigHom Sig₁ Sig₂)
           (τ : SigHom Sig₂ Sig₃)
           (K : Kernel Sig₃ Q)
           where
    _ : KH.KernelHom (Reindex.reindexKernel σ (Reindex.reindexKernel τ K))
                    (Reindex.reindexKernel (composeSigHom σ τ) K)
    _ = HomOverSig.reindexKernel-composeHom σ τ K

    module Assoc = Views.ReindexingAssoc σ τ K
    _ = Assoc.assoc-invL
    _ = Assoc.assoc-invR

  -- Kernel tier-coherence truth lemma (S ↔ H ↔ boundary).
  module _ (K : Kernel Sig Q) where
    module TL = TruthLemma.KernelTruthLemma {Sig = Sig} {Q = Q} K
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    module ST = Truth.StrictTruth Sig
    _ : ∀ (w : LogOSSignature.Cosp Sig) (φ : Kernel.Fml K) →
        Prop._↔_
          (ST.StrictLayer.Sat_S (Kernel.Strict K) w φ)
          (Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.TransH K φ))
    _ = TL.S↔∂

  -- Canonical observer semantics instance from LogicKernel: one-line Obs⋆ construction.
  module _ (K : LogicKernel Sig Q) where
    module O = ObsLK.For {Sig = Sig} {Q = Q} K
    observable⋆ : ∀ {ℓT ℓO} (TruthK : O.Code → Set ℓT) → O.Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
    observable⋆ {ℓT} {ℓO} TruthK = O.Observable⋆ {ℓT = ℓT} {ℓO = ℓO} TruthK

  -- BoundaryIO builder: derived wiring is definitionally the signature wiring.
  module _ (K : Kernel Sig Q) where
    BIO = KBoundary.boundaryIO K
    _ : BoundaryIO.to∂ BIO ≡ LogOSSignature.to∂ Sig
    _ = refl
    _ : BoundaryIO.from∂ BIO ≡ LogOSSignature.from∂ Sig
    _ = refl
    _ : BoundaryIO.sat-coh BIO ≡ Kernel.sat-coh K
    _ = refl

  -- Boundary interlingua: canonical translation and ported closure naturality
  -- (instantiated at the canonical port).
  module _ (K : Kernel Sig Q) where
    open BulkBoundary (Kernel.BB K) using (Con_bnd)

    B = KBoundary.boundaryIO K
    P = Port.canonicalPort B
    module I = Interlingua.For B P P

    translate-id-local : ∀ (c : Con_bnd) → I.translate c ≡ c
    translate-id-local _ = refl

    respects-id : I.Respects≈∂ (λ c → c)
    respects-id eq = eq

    closure-naturality-id
      : ∀ (p : LogOSSignature.∂Cosp Sig) (c : Con_bnd)
      → Prop._↔_
          (Port.BoundaryPort.SatF P p (I.translate (I.Extend₁ (λ x → x) c)))
          (Port.BoundaryPort.SatF P p (I.Extend₂ (λ x → x) (I.translate c)))
    closure-naturality-id =
      I.extend-commutes-with-translate (λ x → x) respects-id

-- Graded 2-cells: the order is refinement on decoded boundary constraints, and the
-- 2-cell calculus composes/whiskers without requiring antisymmetry.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         {K₁ K₂ K₃ : GradedKernel Sig Q}
         where
  open GK2

  -- Composition exists (no equations asserted here; typechecking is the test).
  _ : GradedKernelHom₁ K₂ K₃ → GradedKernelHom₁ K₁ K₂ → GradedKernelHom₁ K₁ K₃
  _ = _∘₁_

-- Flow/Guard transport at the LogicKernel level: “step semantics” is respected
-- by flow-preserving morphisms (lax, preorder-safe).

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         {K₁ K₂ : LogicKernel Sig Q}
         {h : LK2.LogicKernelHom₁ K₁ K₂}
         (hf : LK2.LogicKernelHomFlow₁ h)
         (γ : LogicKernel.Code K₁)
         where
  module FG = Views.FlowGuardTransport {ℓ = ℓ} {Sig = Sig} {Q = Q}
  _ = FG.map-guard-decode≤-LogicKernel hf γ
