{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.TierCategorical where

-- Categorical/tier-graph presentation of S/H/G/R for a kernel.
--
-- This module is intentionally definition-first: it packages existing kernel
-- structure as a small, explicit diagram of carriers, relations, and canonical
-- views into H-tier semantics. No new axioms are introduced.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.RelPreorder
open import LogOS.Minimal.Tier as Tier using (Tier; S; H; G)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.View
open import LogOS.Syntax.Prop as Prop using (_↔_; intro)

open import LogOS.Kernel
open import LogOS.Kernel.Shape as Core hiding (FlowCode)

-- Generic "tier diagram" interface: a family of carriers/relations, with a
-- designated H-tier target and canonical views into that target.

record TierDiagram (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  field
    TierIx       : Set
    TierCarrier  : TierIx → Set ℓ
    TierRel      : TierIx → RelPreorder ℓ ℓ
    HTier        : TierIx
    TierToHView  : (t : TierIx) → View (TierCarrier t) (TierRel HTier)

module TierForKernel
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  open LogOSSignature Sig
  module ST = Truth.StrictTruth Sig

  -- H-tier carrier/ordering target.
  CPᴴ : ConPreorder ℓ
  CPᴴ = BulkBoundary.bnd (Kernel.BB K)

  RPᴴ : RelPreorder ℓ ℓ
  RPᴴ = ConPreorder→RelPreorder CPᴴ

  -- Semantic entailment preorder on S-tier formulas.
  infix 4 _⊑S_
  _⊑S_ : Kernel.Fml K → Kernel.Fml K → Set ℓ
  φ ⊑S ψ =
    ∀ (w : Cosp)
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w φ
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w ψ

  SPreorder : RelPreorder ℓ ℓ
  SPreorder =
    record
      { Con = Kernel.Fml K
      ; _⊑_ = _⊑S_
      ; refl = λ {φ} w satφ → satφ
      ; trans = λ {a} {b} {c} a≤b b≤c w satA → b≤c w (a≤b w satA)
      }

  -- Four-tier index: existing S/H/G plus reflection tier R.
  data Tier4 : Set where
    SHG : Tier → Tier4
    R   : Tier4

  S₄ H₄ G₄ R₄ : Tier4
  S₄ = SHG S
  H₄ = SHG H
  G₄ = SHG G
  R₄ = R

  Carrier₄ : Tier4 → Set ℓ
  Carrier₄ (SHG S) = Kernel.Fml K
  Carrier₄ (SHG H) = ConPreorder.Con CPᴴ
  Carrier₄ (SHG G) = ConPreorder.Con CPᴴ
  Carrier₄ R       = Kernel.Code K

  Rel₄ : Tier4 → RelPreorder ℓ ℓ
  Rel₄ (SHG S) = SPreorder
  Rel₄ (SHG H) = RPᴴ
  Rel₄ (SHG G) = RPᴴ
  Rel₄ R       = ConPreorder→RelPreorder (Core.CodePreorder (Kernel.shape K))

  -- Canonical views into H semantics.
  toHView₄ : (t : Tier4) → View (Carrier₄ t) RPᴴ
  toHView₄ (SHG S) = record { μ = Kernel.TransH K }
  toHView₄ (SHG H) = idView RPᴴ
  toHView₄ (SHG G) = record { μ = GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K)) }
  toHView₄ R       = record { μ = Kernel.decode K }

  -- Pullback relations induced by the chosen tier-view into H.
  infix 4 _⊑tier_ _≈tier_
  _⊑tier_ : ∀ {t : Tier4} → Carrier₄ t → Carrier₄ t → Set ℓ
  _⊑tier_ {t} x y = x ⊑[ toHView₄ t ] y

  _≈tier_ : ∀ {t : Tier4} → Carrier₄ t → Carrier₄ t → Set ℓ
  _≈tier_ {t} x y = x ≈[ toHView₄ t ] y

  Pullback₄ : (t : Tier4) → RelPreorder ℓ ℓ
  Pullback₄ t = PullbackPreorder (toHView₄ t)

  -- The packaged categorical tier diagram for this kernel.
  diagram : TierDiagram ℓ
  diagram =
    record
      { TierIx      = Tier4
      ; TierCarrier = Carrier₄
      ; TierRel     = Rel₄
      ; HTier       = H₄
      ; TierToHView = toHView₄
      }

  -- Useful definitional bridges.
  H-tier↔bnd
    : ∀ {c d}
    → _↔_ (_⊑tier_ {t = H₄} c d)
           (ConPreorder._⊑_ CPᴴ c d)
  H-tier↔bnd = intro (λ x → x) (λ x → x)

  R-tier↔Code≤
    : ∀ {γ δ}
    → _↔_ (_⊑tier_ {t = R₄} γ δ)
           (Core.Code≤ (Kernel.shape K) γ δ)
  R-tier↔Code≤ = intro (λ x → x) (λ x → x)

  -- G-tier action at step/saturation on boundary constraints (explicit names).
  FlowStep : ConPreorder.Con CPᴴ → ConPreorder.Con CPᴴ
  FlowStep = GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))

  FlowSat : ConPreorder.Con CPᴴ → ConPreorder.Con CPᴴ
  FlowSat = GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))

  FlowStep-mono
    : ∀ {c d}
    → ConPreorder._⊑_ CPᴴ c d
    → ConPreorder._⊑_ CPᴴ (FlowStep c) (FlowStep d)
  FlowStep-mono {c} {d} c≤d = GTier.mono (Kernel.G K) {g = GTier.step (Kernel.G K)} c≤d

  FlowSat-infl
    : ∀ c
    → ConPreorder._⊑_ CPᴴ c (FlowSat c)
  FlowSat-infl = GTier.infl-sat (Kernel.G K)

  FlowSat-idemp-lax
    : ∀ c
    → ConPreorder._⊑_ CPᴴ (FlowSat (FlowSat c)) (FlowSat c)
  FlowSat-idemp-lax = GTier.idemp-sat (Kernel.G K)

  Th*-fixed-sat
    : _≈CP_ CPᴴ
        (GTier.Th* (Kernel.G K))
        (FlowSat (GTier.Th* (Kernel.G K)))
  Th*-fixed-sat = GTier.Th*-fixed≈ (Kernel.G K)
