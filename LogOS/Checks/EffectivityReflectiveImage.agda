{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.EffectivityReflectiveImage where

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc)
open import LogOS.Syntax.Prop using (intro)
open import LogOS.LT.ConPreorder using (ConPreorder; refl⊑)
open import LogOS.LT.Flow using (Stable; mkStable; elem)
open import LogOS.LT.Theorems.AbstractGaloisConnection using
  ( GaloisConnection
  ; RightImagePoint
  ; closure
  ; stableReflectiveImage
  )
open import LogOS.LT.Effectivity using
  ( effectivityFromGalois
  ; effectivityFromGalois-stableReflectiveImage
  )
open import LogOS.Ports.Residuals using
  ( weakestPreconditionStableRepresentation )
open import LogOS.Ports.Universality.NatBoundary using (NatBoundary)

identityGalois : GaloisConnection NatBoundary NatBoundary
identityGalois =
  record
    { L = λ n → n
    ; R = λ n → n
    ; L-mono = λ n≤m → n≤m
    ; R-mono = λ n≤m → n≤m
    ; adj = λ _ _ → intro (λ n≤m → n≤m) (λ n≤m → n≤m)
    }

twoStable
  : Stable {CP = NatBoundary} (LogOS.LT.Flow.GuardedClosure.Flow (closure identityGalois))
twoStable =
  mkStable
    (suc (suc zero))
    (refl⊑ NatBoundary)

_ : RightImagePoint identityGalois (elem twoStable)
_ = stableReflectiveImage identityGalois twoStable

_ : RightImagePoint identityGalois (elem twoStable)
_ = effectivityFromGalois-stableReflectiveImage identityGalois twoStable

_ : RightImagePoint identityGalois (elem twoStable)
_ = weakestPreconditionStableRepresentation identityGalois twoStable

_ : Stable {CP = NatBoundary}
      (LogOS.LT.Flow.GuardedClosure.Flow
        (LogOS.LT.Effectivity.Effectivity.GC (effectivityFromGalois identityGalois)))
_ = twoStable
