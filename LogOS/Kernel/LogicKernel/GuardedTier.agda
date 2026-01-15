{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.GuardedTier where

-- Unified guarded-tier surface + adapters between ungraded and graded closures.

open import LogOS.Prelude

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.LogicKernel using (GTier)

-- Preferred name for the logic-kernel guarded tier.
GuardedTier = GTier

private
  module GC = Truth.GuardedCore

fromGuardedClosure
  : ∀ {ℓ : Level} {Q : QAdapter ℓ} {CP : ConPoset ℓ}
  → GC.GuardedClosure CP
  → GuardedTier Q CP
fromGuardedClosure G =
  record
    { Step      = ⊤
    ; step      = tt
    ; sat       = tt
    ; Flow      = λ _ c → GC.GuardedClosure.Flow G c
    ; mono      = GC.GuardedClosure.mono G
    ; infl-sat  = GC.GuardedClosure.infl G
    ; idemp-sat = GC.GuardedClosure.idemp-lax G
    ; Th*       = GC.GuardedClosure.Th* G
    ; Th*-fixed = GC.GuardedClosure.Th*-fixed G
    }

fromGradedClosure
  : ∀ {ℓ : Level} {Q : QAdapter ℓ} {CP : ConPoset ℓ}
  → GC.GradedClosure Q CP
  → QAdapter.Scale Q
  → GuardedTier Q CP
fromGradedClosure {Q = Q} G step =
  record
    { Step      = QAdapter.Scale Q
    ; step      = step
    ; sat       = GC.GradedClosure.sat G
    ; Flow      = GC.GradedClosure.Flow G
    ; mono      = GC.GradedClosure.mono G
    ; infl-sat  = GC.GradedClosure.infl-sat G
    ; idemp-sat = GC.GradedClosure.idemp-sat G
    ; Th*       = GC.GradedClosure.Th* G
    ; Th*-fixed = GC.GradedClosure.Th*-fixed G
    }

fromGradedClosure-sat
  : ∀ {ℓ : Level} {Q : QAdapter ℓ} {CP : ConPoset ℓ}
  → GC.GradedClosure Q CP
  → GuardedTier Q CP
fromGradedClosure-sat G = fromGradedClosure G (GC.GradedClosure.sat G)

toGuardedClosure
  : ∀ {ℓ : Level} {Q : QAdapter ℓ} {CP : ConPoset ℓ}
  → GuardedTier Q CP
  → GC.GuardedClosure CP
toGuardedClosure G =
  record
    { Flow      = λ c → GTier.Flow G (GTier.sat G) c
    ; mono      = GTier.mono G
    ; infl      = GTier.infl-sat G
    ; idemp-lax = GTier.idemp-sat G
    ; Th*       = GTier.Th* G
    ; Th*-fixed = GTier.Th*-fixed G
    }
