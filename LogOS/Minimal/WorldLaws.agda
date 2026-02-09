{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.WorldLaws where

open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.World

-- Optional law layers for `WorldH`.
--
-- The Minimal core keeps `_≤ctx_` as a raw relation (used only via monotonicity
-- of satisfaction). When you want to treat worlds as a preorder/category of
-- contexts, supply the preorder laws explicitly via `CtxPreorder`.

module For {ℓ : Level} (Sig : LogOSSignature ℓ) where
  module W = Worlds Sig
  open W

  record CtxPreorder (Q : QAdapter ℓ) (WH : WorldH Q) : Set (lsuc ℓ) where
    open WorldH WH
    field
      ≤ctx-refl  : ∀ {w} → _≤ctx_ w w
      ≤ctx-trans : ∀ {w w' w''} → _≤ctx_ w w' → _≤ctx_ w' w'' → _≤ctx_ w w''

  -- Package `_≤ctx_` as a `ConPreorder` on worlds (carrier = `Cosp`).
  ctxPreorder
    : ∀ {Q : QAdapter ℓ} {WH : WorldH Q}
      (L : CtxPreorder Q WH)
    → ConPreorder ℓ
  ctxPreorder {WH = WH} L =
    let
      open WorldH WH
      open CtxPreorder L
    in
    record
      { Con   = WorldS
      ; _⊑_   = _≤ctx_
      ; refl  = ≤ctx-refl
      ; trans = ≤ctx-trans
      }
