{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Agreement.Definitional where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View.Strictification using (_≃[_]_)
open import LogOS.Ports.Universality.Agreement using (AgreementPort)

infix 4 _≃A_ _≃B_

_≃A_
  : ∀ {ℓCode ℓConA ℓRelA ℓConB ℓRelB}
    {X : Set ℓCode}
    {A : ConPreorder ℓConA ℓRelA}
    {B : ConPreorder ℓConB ℓRelB}
  → (P : AgreementPort X A B)
  → X → X → Set ℓConA
_≃A_ P x y = x ≃[ AgreementPort.viewA P ] y

_≃B_
  : ∀ {ℓCode ℓConA ℓRelA ℓConB ℓRelB}
    {X : Set ℓCode}
    {A : ConPreorder ℓConA ℓRelA}
    {B : ConPreorder ℓConB ℓRelB}
  → (P : AgreementPort X A B)
  → X → X → Set ℓConB
_≃B_ P x y = x ≃[ AgreementPort.viewB P ] y
