{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.World where

open import LogOS.Prelude
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

-- Minimal worlds by tier, over an existing signature Sig

module Worlds {ℓ : Level} (Sig : LogOSSignature ℓ) where
  open LogOSSignature Sig

  -- S-tier: strict worlds are just structured cospans
  WorldS : Set ℓ
  WorldS = Cosp

  -- H-tier: same carrier, enriched with context and Q-weighted flow
  record WorldH (Q : QAdapter ℓ) : Set (lsuc ℓ) where
    infix 4 _≤ctx_
    open QAdapter Q renaming (Scale to Scl; _≤s_ to _≤Scl_; _·_ to _∙_; e to ε)
    field
      -- Context preorder (Kripke-style)
      _≤ctx_ : Cosp → Cosp → Set ℓ

      -- Q-weighted world-flow between worlds (Q-category shape)
      WFlow  : Cosp → Cosp → Scl

      -- Lax laws for flows (declarations for intended structure)
      wflow-refl  : ∀ (w : Cosp) → _≤Scl_ ε (WFlow w w)
      wflow-trans : ∀ (w w' w'' : Cosp) → _≤Scl_ (WFlow w w' ∙ WFlow w' w'') (WFlow w w'')

  -- G-tier: guarded use of the same carrier (step-indexed/time-indexed)
  -- Design: reuse the H-world structure. Guardedness lives in Flow/μ (see Minimal.Truth),
  -- not in a distinct carrier. This keeps the carrier minimal and pushes guarded structure
  -- into the closure and fixed-point interfaces where it belongs.
  WorldG : (Q : QAdapter ℓ) → Set (lsuc ℓ)
  WorldG Q = WorldH Q
