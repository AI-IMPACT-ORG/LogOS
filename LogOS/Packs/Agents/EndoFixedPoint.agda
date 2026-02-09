{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.EndoFixedPoint where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
import LogOS.Packs.Agents.EndoFixedPointCore as Core

-- Shared fixed-point wrappers for endomaps in application packs.
-- These are lightweight adapters around the kernel-level Kleene μ utilities.

module Kernel where
  open import LogOS.Kernel using (Kernel)
  import LogOS.Kernel.Endo as LKEndo
  import LogOS.Theorems.Boundary.Kernel.Mu as LKMu

  module For
    {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
              (BulkBoundary.bnd (Kernel.BB K)))
    where

    open Kernel K using (BB)
    open BulkBoundary BB using (Con_bnd)
    open LKEndo

    module μ = LKMu.Kleene Sig Q K ωCPO
    open μ
    private
      MonoOn' : (Con_bnd → Con_bnd) → Set _
      MonoOn' F = ∀ {c d} → _⊑_ c d → _⊑_ (F c) (F d)

      KO : Core.KleeneOps Con_bnd
      KO =
        record
          { _⊑_ = _⊑_
          ; MonoOn = MonoOn'
          ; iter = iter
          ; μF = μF
          ; μF-unfold-left = μF-unfold-left
          ; μF-induction = μF-induction
          ; ScottContinuous = ScottContinuous
          ; μF-unfold-right = μF-unfold-right
          ; iter-mono-chain-infl = iter-mono-chain-infl
          ; μF-unfold-right-infl = μF-unfold-right-infl
          }

      EO : Core.EndoOps Con_bnd _⊑_ MonoOn'
      EO = record { Endo = Endo K ; fn = Endo.fn ; mono = Endo.mono }

    module FP = Core.For KO EO
    open FP public using
      (_⊑_; iter; μF; μF-unfold-left; μF-induction; ScottContinuous;
       μF-unfold-right; iter-mono-chain-infl; μF-unfold-right-infl;
       Policy; iterEndo; muEndo; muEndo-unfold-left; muEndo-induction;
       iterEndo-mono-chain-infl; muEndo-unfold-right; muEndo-unfold-right-infl)

module Graded where
  open import LogOS.Kernel.Graded using (GradedKernel)
  import LogOS.Kernel.Graded.Endo as GEndo
  import LogOS.Theorems.Boundary.Graded.Mu as GMu

  module For
    {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
              (BulkBoundary.bnd (GradedKernel.BB K)))
    where

    open GradedKernel K using (BB)
    open BulkBoundary BB using (Con_bnd)
    open GEndo

    module μ = GMu.Kleene Sig Q K ωCPO
    open μ
    private
      MonoOn' : (Con_bnd → Con_bnd) → Set _
      MonoOn' F = ∀ {c d} → _⊑_ c d → _⊑_ (F c) (F d)

      KO : Core.KleeneOps Con_bnd
      KO =
        record
          { _⊑_ = _⊑_
          ; MonoOn = MonoOn'
          ; iter = iter
          ; μF = μF
          ; μF-unfold-left = μF-unfold-left
          ; μF-induction = μF-induction
          ; ScottContinuous = ScottContinuous
          ; μF-unfold-right = μF-unfold-right
          ; iter-mono-chain-infl = iter-mono-chain-infl
          ; μF-unfold-right-infl = μF-unfold-right-infl
          }

      EO : Core.EndoOps Con_bnd _⊑_ MonoOn'
      EO = record { Endo = Endo K ; fn = Endo.fn ; mono = Endo.mono }

    module FP = Core.For KO EO
    open FP public using
      (_⊑_; iter; μF; μF-unfold-left; μF-induction; ScottContinuous;
       μF-unfold-right; iter-mono-chain-infl; μF-unfold-right-infl;
       Policy; iterEndo; muEndo; muEndo-unfold-left; muEndo-induction;
       iterEndo-mono-chain-infl; muEndo-unfold-right; muEndo-unfold-right-infl)
