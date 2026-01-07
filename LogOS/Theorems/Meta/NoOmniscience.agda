{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.NoOmniscience where

-- ============================================================================
-- Diagonal obstruction for total observers (no-omniscience form).
--
-- Under a Tarski-style diagonalisation principle restricted to *decidable*
-- predicates (`TruthDiagonal`), there is no total decider/observer for a
-- truth-like predicate. Equivalently, any candidate “total oracle” must fail on
-- some explicit code. This module packages that pattern for
-- `SpectralSeparationOutput`.
-- ============================================================================

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; ¬_; ⊥; to)

open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Theorems.Meta.Base using (DeciderC)
open import LogOS.Theorems.Meta.Assumptions.Diagonal using (TruthDiagonal; TruthDiagonalC)
open import LogOS.Theorems.Meta.Tarski as Tarski
open import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO

-- No total, decode-extensional separation oracle: diagonalization forces an
-- explicit "undefined" input (event horizon).

eventHorizon
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (SS : SSO.SpectralSeparationOutput K)
  → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation SS)
  → Σ (Kernel.Code K) (λ γ → SSO.SpectralSeparationOutput.NoSeparation SS γ)
eventHorizon SS TD =
  SSO.separation-output-diagonal-witness SS TD

noTotalOracle
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (SS : SSO.SpectralSeparationOutput K)
  → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation SS)
  → ¬ (∀ γ → SSO.SpectralSeparationOutput.HasSeparation SS γ)
noTotalOracle SS TD =
  SSO.separation-output-not-total SS TD

noSelfCertifiedTotality
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
    (SS : SSO.SpectralSeparationOutput K)
    (TC : SSO.SeparationTotalityClaim SS)
  → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation SS)
  → SSO.SeparationTotalityClaim.Totality TC
  → ⊥
noSelfCertifiedTotality SS TC TD t =
  SSO.separation-output-no-self-certification SS TD TC t

-- Deciders are a special case of "omniscient observers": if liars exist for a
-- truth-like predicate, then there is no total decider for it.

noOmniscientDecider
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓ)
  → TruthDiagonal K TruthK
  → ¬ (DeciderC {Sig = Sig} {Q = Q} {K = K} TruthK)
noOmniscientDecider K TruthK TD =
  Tarski.undef-classical K TruthK TD

-- Code-generic form (graded-kernel friendly):
-- diagonalisation against decidable observers blocks total decidability.
noOmniscientDeciderC
  : ∀ {ℓCode ℓT : Level}
    (Code   : Set ℓCode)
    (TruthK : Code → Set ℓT)
  → TruthDiagonalC Code TruthK
  → ¬ (∀ γ → TruthK γ ⊎ ¬ TruthK γ)
noOmniscientDeciderC Code TruthK TD dec =
  go (dec γ)
  where
    open _↔_
    open TruthDiagonalC TD

    liar = liarForDecider TruthK dec
    γ    = proj₁ liar
    eqv  = proj₂ liar

    go : TruthK γ ⊎ ¬ TruthK γ → ⊥
    go (inj₁ t)  = to eqv t t
    go (inj₂ nt) = nt (_↔_.from eqv nt)
