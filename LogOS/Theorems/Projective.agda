{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Projective where

open import LogOS.Prelude

open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World

-- Generic (lax) projector on a constraint preorder.
--
-- This module provides the tier-specific *instances* of the shared projector
-- shape and reexports the core definitions for convenience.

open import LogOS.Theorems.Reflection.Projector public

-- Regularization view (module header note):
-- A Projector (nucleus) is a renormalization step on boundary truth: it is a
-- closure operator (inflationary, idempotent-lax). Its fixed points are the
-- stabilized truths. Instances arise from Flow (G-tier) and invariance
-- (H-tier), offering an operator-free fixed-point semantics complementary to
-- the HPFlow intertwining.

-- Instances

-- From a GuardedClosure on CP

module ForG {ℓ}
            {Sig : LogOS.Base.Signature.LogOSSignature ℓ}
            {Q   : QAdapter ℓ}
            where
  open Truth.GuardedTruth Sig Q

  fromGuarded
    : ∀ {CP : ConPreorder ℓ}
      (GC : GuardedClosure CP)
    → Projector CP
  fromGuarded GC = record
    { P = GuardedClosure.Flow GC
    ; infl = GuardedClosure.infl GC
    ; idemp-lax = GuardedClosure.idemp-lax GC
    }

-- From H-tier invariance on the boundary preorder

module ForH {ℓ}
             {Sig : LogOS.Base.Signature.LogOSSignature ℓ}
             {Q   : QAdapter ℓ}
             (W   : Worlds.WorldH Sig Q)
             where
  open Truth.HomotypicalTruth Sig Q W

  fromInvariance
    : (BB : BulkBoundary ℓ)
    → Invariance BB
    → Projector (BulkBoundary.bnd BB)
  fromInvariance BB Inv = record
    { P = Invariance.Inv_H Inv
    ; infl = Invariance.infl Inv
    ; idemp-lax = Invariance.idemp-lax Inv
    }

-- From a graded guarded closure by taking the saturation grade.

module ForGraded {ℓ} {Q : QAdapter ℓ} where
  module GT = Truth.GuardedCore

  fromGradedSat
    : ∀ {CP : ConPreorder ℓ}
      (GC : GT.GradedClosure Q CP)
    → Projector CP
  fromGradedSat {CP = CP} GC =
    let open ConPreorder CP
        open GT.GradedClosure GC
    in record
         { P = Flow sat
         ; infl = infl-sat
         ; idemp-lax = idemp-sat
         }
