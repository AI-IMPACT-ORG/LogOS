{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.HP.Opacity where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥)

open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface

import LogOS.Domain.Opacity.NumberTheory.HP.Flow as HPFlow

open import LogOS.Theorems.Meta.Assumptions.Diagonal using (TruthDiagonal)
import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO

-- “Opacity” theorem for Hilbert–Pólya style operators:
--
-- If you treat some HP-linked predicate as “truth-like” (it admits a Tarski-style
-- liar via `TruthDiagonal`), then there cannot exist a *total*, extensional
-- certificate oracle for it. In particular, any extensional oracle must leave
-- some input explicitly “undefined”.
--
-- This is the formal version of:
-- “a fully explicit, total ‘spectral certificate oracle’ for the global object is blocked”.

module For
  {ℓ}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  (HP  : HPInterface K)
  where

  open Kernel K
  open HPInterface HP

  Con∂ : Set ℓ
  Con∂ = ConPreorder.Con (BulkBoundary.bnd BB)

  -- Boundary predicate: Op fixes the embedded boundary constraint.
  OpFixed∂ : Con∂ → Set ℓ
  OpFixed∂ c = Op (embed c) ≡ embed c

  -- A certificate oracle for Op-fixedness, extensional up to decoded observational equality.
  --
  -- `infer γ` either produces a certificate for the *decoded* boundary constraint,
  -- or explicitly returns `inj₂ tt` (undefined / no certificate).
  record OpFixedOracle : Set (lsuc (lsuc ℓ)) where
    field
      oracle : SSO.Oracle K (Σ Con∂ OpFixed∂)

      correct : ∀ γ {c} {pf : OpFixed∂ c} →
        SSO.Oracle.infer oracle γ ≡ inj₁ (c , pf) → c ≡ decode γ

    open SSO.Oracle oracle public using (infer; ext)

  -- View an OpFixedOracle as a generic partial-output surface.
  toSSO : OpFixedOracle → SSO.SpectralSeparationOutput K
  toSSO O = SSO.Oracle.toSSO (OpFixedOracle.oracle O)

  -- Budgeted/graded strengthening: rule out any oracle that is both
  -- (i) extensional and (ii) total *within a given budget predicate*.
  --
  -- This is the quantale/grade-friendly form of opacity: you can allow witnesses
  -- to exist in principle, but no single budget function can make them uniformly
  -- available everywhere under diagonalisation.

  module Budgeted (O : OpFixedOracle) where
    module GB = SSO.GeneralB (toSSO O)
    open GB public using (WitnessCostB)
    module General = GB.General

  -- Extract: whenever the oracle returns a witness, it is a proof that Op fixes
  -- the decoded boundary constraint.
  oracle-sound
    : ∀ (O : OpFixedOracle) (γ : Code)
      → SSO.SpectralSeparationOutput.HasSeparation (toSSO O) γ
      → OpFixed∂ (decode γ)
  oracle-sound O γ (w , eq) with w
  ... | (c , pf) =
    subst OpFixed∂ (OpFixedOracle.correct O γ {c = c} {pf = pf} eq) pf

  -- With faithfulness, Op-fixed certificates are exactly Flow-fixed certificates.
  oracle-sound→Flow-fixed
    : ∀ (O : OpFixedOracle)
      → EmbedFaithful K HP
      → ∀ γ
      → SSO.SpectralSeparationOutput.HasSeparation (toSSO O) γ
      → Endo.fn (Flow-Endo K) (decode γ) ≡ decode γ
  oracle-sound→Flow-fixed O EF γ has =
    HPFlow.Op-fixed→Flow-fixed K HP EF (decode γ) (oracle-sound O γ has)

  -- Main theorem: if “having a certificate for Op-fixedness” is truth-diagonalizable,
  -- then a total oracle is impossible. In particular, diagonalization forces an
  -- explicit γ where the oracle returns `inj₂ tt`.
  hp-oracle-not-total
    : ∀ (O : OpFixedOracle)
      → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation (toSSO O))
      → Σ Code (λ γ → SSO.SpectralSeparationOutput.NoSeparation (toSSO O) γ)
  hp-oracle-not-total O TD =
    SSO.separation-output-diagonal-witness (toSSO O) TD

  -- Corollary form: no OpFixedOracle can be total (defined everywhere) under the
  -- same diagonal principle.
  hp-oracle-no-total-function
    : ∀ (O : OpFixedOracle)
      → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation (toSSO O))
      → ¬ (∀ γ → SSO.SpectralSeparationOutput.HasSeparation (toSSO O) γ)
  hp-oracle-no-total-function O TD =
    SSO.separation-output-not-total (toSSO O) TD

  -- Strongest form: even a *self-certified* totality claim collapses under diagonalization.
  hp-oracle-no-self-certification
    : ∀ (O : OpFixedOracle)
      → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation (toSSO O))
      → (TC : SSO.SeparationTotalityClaim (toSSO O))
      → SSO.SeparationTotalityClaim.Totality TC
      → ⊥
  hp-oracle-no-self-certification O TD TC t =
    SSO.separation-output-no-self-certification (toSSO O) TD TC t
