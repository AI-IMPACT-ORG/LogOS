{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Conventions.FlowStabilisation where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Flow-idemp≈)

flow-stabilises≈
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → ∀ c → _≈_ CP (Flow GC (Flow GC c)) (Flow GC c)
flow-stabilises≈ = Flow-idemp≈
