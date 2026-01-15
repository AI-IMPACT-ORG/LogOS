{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Safety.Matrix where

-- A single, paper-facing matrix of paradox gates, anchored to the architecture.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.Safety.ArchitectureFromSafety as Arch
import LogOS.Theorems.Meta.Safety.AvoidanceList as Avoid

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  where

  module A = Arch.For K

  record SafetyMatrix : Set (lsuc (lsuc ℓ)) where
    field
      architecture        : A.Architecture
      Russell             : Set (lsuc ℓ)
      BuraliForti         : Set (lsuc ℓ)
      TruthDiagonal       : Set (lsuc ℓ)
      Godel               : Set (lsuc ℓ)
      Curry               : Set (lsuc ℓ)
      Berry               : Set (lsuc ℓ)
      UnsafeReflection    : Set (lsuc ℓ)
      UnrestrictedFixpoint : Set (lsuc ℓ)
      Explosion           : Set (lsuc ℓ)

  safetyMatrix : SafetyMatrix
  safetyMatrix =
    record
      { architecture = A.architecture
      ; Russell = Avoid.RussellRequires {ℓ = ℓ}
      ; BuraliForti = Avoid.BuraliFortiRequires {ℓ = ℓ}
      ; TruthDiagonal = Avoid.TruthDiagonalRequires K
      ; Godel = Avoid.GodelRequires K
      ; Curry = Avoid.CurryRequires K
      ; Berry = Avoid.BerryRequires K
      ; UnsafeReflection = Avoid.UnsafeReflection K
      ; UnrestrictedFixpoint = Avoid.UnrestrictedFixpoint K
      ; Explosion = Avoid.Explosion K
      }
