{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.MathPhysSynthesis where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
open import LogOS.Kernel
open import LogOS.Kernel.Graded as GK using (GradedKernel)

import LogOS.Theorems.Meta.Assumptions.Diagonal as Diag
import LogOS.Theorems.Meta.ObserverCore as ObsCore

-- ============================================================================
-- MathPhysSynthesis
--
-- A metalogical observer-semantics bundle that is intended to sit at the
-- interface between:
-- - “math”: truth predicates on a code language, and
-- - “physics”: what is observable/communicable under a dynamics (a step) and
--   a representation-invariance discipline (decode-extensionality).
--
-- It is *representation-first*: the core is a Code language with a step and a
-- decode map. This makes the same bundle instantiate equally well for:
-- - `Kernel.Code` / `Kernel.FlowCode`, and
-- - `GradedKernel.Code` / `GradedKernel.FlowCode`,
-- without forcing graded → ungraded forgetful conversions.
-- ============================================================================

module Observer
  {ℓCode ℓDec ℓT : Level}
  (Code   : Set ℓCode)
  (Dec    : Set ℓDec)
  (decode : Code → Dec)
  (step   : Code → Code)
  (TruthK : Code → Set ℓT)
  where

  DecodeExtensional
    : ∀ {ℓP} (P : Code → Set ℓP) → Set (ℓCode ⊔ ℓDec ⊔ ℓP)
  DecodeExtensional P = ObsCore.DecodeExtensional decode P

  record AdmissibleObs {ℓO : Level} (Obs : Code → Set ℓO)
    : Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ ℓO) where
    field
      core : ObsCore.Admissible Code Dec decode step TruthK Obs

    open ObsCore.Admissible core public

  -- “Largest admissible observability” (a la Comm⋆ / Pr):
  -- Obs⋆ γ holds if there exists some admissible Obs that contains γ.
  --
  -- Universe note: `Obs⋆` quantifies over predicates `Obs : Code → Set ℓO`, so
  -- it lives one universe higher (in `… ⊔ lsuc ℓO`). Choosing a larger `ℓO`
  -- allows witness-carrying observers; choosing a smaller `ℓO` tightens
  -- pack-facing types but restricts what counts as an “observer”.
  Obs⋆
    : ∀ {ℓO : Level} → Code → Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ lsuc ℓO)
  Obs⋆ {ℓO = ℓO} γ =
    Σ (Code → Set ℓO) (λ Obs → AdmissibleObs {ℓO = ℓO} Obs × Obs γ)

  Pr : ∀ {ℓO : Level} → Code → Set (ℓCode ⊔ ℓDec ⊔ ℓT ⊔ lsuc ℓO)
  Pr {ℓO = ℓO} = Obs⋆ {ℓO = ℓO}

  Pr-sound
    : ∀ {ℓO : Level} {γ}
      → Pr {ℓO = ℓO} γ
      → TruthK γ
  Pr-sound (_ , (A , oγ)) = AdmissibleObs.sound A oγ

  Pr-stable
    : ∀ {ℓO : Level} (γ : Code)
      → Pr {ℓO = ℓO} γ ↔ Pr {ℓO = ℓO} (step γ)
  Pr-stable {ℓO = ℓO} γ =
    record { to = to′ ; from = from′ }
    where
      open _↔_
      to′ : Pr {ℓO = ℓO} γ → Pr {ℓO = ℓO} (step γ)
      to′ (Obs , (A , oγ)) =
        let st = AdmissibleObs.stable A γ in
        Obs , (A , _↔_.to st oγ)

      from′ : Pr {ℓO = ℓO} (step γ) → Pr {ℓO = ℓO} γ
      from′ (Obs , (A , oγ′)) =
        let st = AdmissibleObs.stable A γ in
        Obs , (A , _↔_.from st oγ′)

  Pr-ext
    : ∀ {ℓO : Level}
      → DecodeExtensional (Pr {ℓO = ℓO})
  Pr-ext {ℓO = ℓO} γ₁ γ₂ decEq (Obs , (A , o₁)) =
    let o₂ = AdmissibleObs.ext A γ₁ γ₂ decEq o₁ in
    Obs , (A , o₂)

-- ============================================================================
-- The bundled axiom surface: diagonalisation against decidable observers.
-- ============================================================================

record MathPhysSynthesis {ℓCode ℓDec ℓT : Level}
                         (Code   : Set ℓCode)
                         (Dec    : Set ℓDec)
                         (decode : Code → Dec)
                         (step   : Code → Code)
                         (TruthK : Code → Set ℓT)
                         : Set (lsuc (ℓCode ⊔ ℓDec ⊔ ℓT)) where
  field
    diagonal : Diag.TruthDiagonalC Code TruthK

  open Observer Code Dec decode step TruthK public

-- Kernel instance helper: choose `Code = Kernel.Code K`, `step = FlowCode K`.
fromKernel
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓ)
  → Diag.TruthDiagonal K TruthK
  → MathPhysSynthesis (Kernel.Code K)
                      (ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
                      (Kernel.decode K)
                      (FlowCode K)
                      TruthK
fromKernel K TruthK TD =
  record { diagonal = Diag.TruthDiagonal→TruthDiagonalC TruthK TD }

-- Kernel instance helper (fully polymorphic): accept diagonalisation directly at
-- the code language level, without the level restriction of `TruthDiagonal`.
fromKernelC
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Diag.TruthDiagonalC (Kernel.Code K) TruthK
  → MathPhysSynthesis (Kernel.Code K)
                      (ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
                      (Kernel.decode K)
                      (FlowCode K)
                      TruthK
fromKernelC K TruthK TD =
  record { diagonal = TD }

-- Graded-kernel instance helper: choose `Code = GradedKernel.Code K`, `step = FlowCode K`.
--
-- This does not require collapsing a graded kernel to an ungraded one. The
-- diagonal principle is supplied directly at the code language level.
fromGradedKernel
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (TruthK : GradedKernel.Code K → Set ℓT)
  → Diag.TruthDiagonalC (GradedKernel.Code K) TruthK
  → MathPhysSynthesis (GradedKernel.Code K)
                      (ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K)))
                      (GradedKernel.decode K)
                      (GK.FlowCode K)
                      TruthK
fromGradedKernel K TruthK TD =
  record { diagonal = TD }
