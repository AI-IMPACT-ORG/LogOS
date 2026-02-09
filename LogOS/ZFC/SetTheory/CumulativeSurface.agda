{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.CumulativeSurface where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel

open import LogOS.ZFC.SetTheory.Cumulative
open import LogOS.ZFC.SetTheory.Dsl
open import LogOS.ZFC.SetTheory.LimitPack using (toZFAxioms)

-- Promote any stage-based cumulative hierarchy with a boundary realisation into
-- the tensor/endomap DSL surface. This is the recommended pipeline:
--   StageToCH + boundary realisation → ZFDsl → `toZFAxioms` (if you need the
--   classical ZF surface).

stageToSurface
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (S2H : StageToCH K)
  → ZFDsl K
stageToSurface K S2H = record
  { axioms        = toZFAxioms K CH
  ; realise       = realise∞
  ; mem⇒flow      = mem⇒flow∞
  ; eq⇒realise≡   = eq⇒realise∞≡
  ; tf-stable     = tf-stable∞
  }
  where
    open StageToCH S2H
