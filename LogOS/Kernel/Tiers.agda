{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Tiers where

-- ============================================================================
-- S/H/G/R TIER ALIGNMENT (DERIVED INTERFACE)
--
-- This module makes the “four tiers” explicit for any `Kernel`:
-- - S-tier: strict satisfaction `Sat_S`
-- - H-tier: homotypical satisfaction `Sat_H` and boundary satisfaction `Sat_H_bnd`
-- - G-tier: guarded flow `Flow` and distinguished fixed-point witness `Th*`
-- - R-tier: reflection layer `Code` with derived satisfaction `Sat_R` via `decode`
--
-- Everything here is *derived* from the kernel interface: no new axioms.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.RelPreorder
open import LogOS.Minimal.View
open import LogOS.Syntax.Prop as Prop

open import LogOS.Kernel
open import LogOS.Kernel.Shape as Core hiding (FlowCode)

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  open LogOSSignature Sig
  module ST = Truth.StrictTruth Sig
  module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)

  -- ------------------------------------------------------------------------
  -- Canonical view targets (order-theoretic + observational).
  --
  -- These are exported so domain-specific relations can be introduced as
  -- pullbacks along explicit views (`LogOS.Minimal.View`), rather than by
  -- ad-hoc glyph overloading.

  -- Base H-target preorder (order-theoretic).
  CPᴴ : ConPreorder ℓ
  CPᴴ = BulkBoundary.bnd (Kernel.BB K)

  -- Same target, but in the generic two-level preorder interface (so it can be
  -- used uniformly alongside observational targets).
  RPᴴ : RelPreorder ℓ ℓ
  RPᴴ = ConPreorder→RelPreorder CPᴴ

  -- Observational H-target preorder induced by boundary satisfaction.
  --
  -- Target relation: `c ⊑ᵒ d` iff every boundary observation that satisfies `c`
  -- also satisfies `d`. Mutual refinement is then definitionally `≈` in this
  -- preorder (`Obs≈`).
  CPᴴᵒ : RelPreorder ℓ ℓ
  CPᴴᵒ = ObsPreorder (Kernel.Sat_H_bnd K)

  -- Canonical views into the H-target preorder.
  decodeView : View (Kernel.Code K) RPᴴ
  decodeView = record { μ = Kernel.decode K }

  transHView : View (Kernel.Fml K) RPᴴ
  transHView = record { μ = Kernel.TransH K }

  -- Convenience: R-tier satisfaction as an observational view target.
  --
  -- This view is the canonical "semantic target" for code-level observational
  -- comparisons (use `ObsPreorder`/`Obs≈`).
  decodeObsView : View (Kernel.Code K) CPᴴᵒ
  decodeObsView = record { μ = Kernel.decode K }

  -- ------------------------------------------------------------------------
  -- View-named relations (recommended for downstream naming discipline).
  --
  -- These are definitional sugar for the generic pullback relations from
  -- `LogOS.Minimal.View`. They are intentionally named by the view.

  infix 4 _⊑decode_ _≈decode_ _≃decode_

  _⊑decode_ : Kernel.Code K → Kernel.Code K → Set ℓ
  γ ⊑decode δ = γ ⊑[ decodeView ] δ

  _≈decode_ : Kernel.Code K → Kernel.Code K → Set ℓ
  γ ≈decode δ = γ ≈[ decodeView ] δ

  _≃decode_ : Kernel.Code K → Kernel.Code K → Set ℓ
  γ ≃decode δ = γ ≃[ decodeView ] δ

  infix 4 _⊑TransH_ _≈TransH_ _≃TransH_

  _⊑TransH_ : Kernel.Fml K → Kernel.Fml K → Set ℓ
  φ ⊑TransH ψ = φ ⊑[ transHView ] ψ

  _≈TransH_ : Kernel.Fml K → Kernel.Fml K → Set ℓ
  φ ≈TransH ψ = φ ≈[ transHView ] ψ

  _≃TransH_ : Kernel.Fml K → Kernel.Fml K → Set ℓ
  φ ≃TransH ψ = φ ≃[ transHView ] ψ

  -- Observational (satisfaction-induced) comparisons on code via `decode`.

  infix 4 _⊑obs_ _≈obs_

  _⊑obs_ : Kernel.Code K → Kernel.Code K → Set ℓ
  γ ⊑obs δ = γ ⊑[ decodeObsView ] δ

  _≈obs_ : Kernel.Code K → Kernel.Code K → Set ℓ
  γ ≈obs δ = γ ≈[ decodeObsView ] δ

  -- Non-glyph alias (useful at call sites that prefer a prefix name).
  Obs≈obs : Kernel.Code K → Kernel.Code K → Set ℓ
  Obs≈obs = _≈obs_

  -- Presentation aliases for observational comparisons on code via `decode`.
  --
  -- These are logically equivalent to `_⊑obs_` / `_≈obs_` but keep the
  -- pointwise `_↔_` presentation available when needed.

  Sat_obs : ∂Cosp → Kernel.Code K → Set ℓ
  Sat_obs p γ = Kernel.Sat_H_bnd K p (Kernel.decode K γ)

  ObsLeobs : Kernel.Code K → Kernel.Code K → Set ℓ
  ObsLeobs = Prop.ObsLeOn Sat_obs

  ObsEqobs : Kernel.Code K → Kernel.Code K → Set ℓ
  ObsEqobs = Prop.ObsEqOn Sat_obs

  ObsEqobs↔≈obs : ∀ {γ δ} → Prop._↔_ (ObsEqobs γ δ) (γ ≈obs δ)
  ObsEqobs↔≈obs {γ} {δ} =
    ObsEqOn↔Obs≈ Sat_obs {x = γ} {y = δ}

  ObsEqobs↔Obs≈obs : ∀ {γ δ} → Prop._↔_ (ObsEqobs γ δ) (Obs≈obs γ δ)
  ObsEqobs↔Obs≈obs = ObsEqobs↔≈obs

  -- ------------------------------------------------------------------------
  -- R-tier (reflection) as “decoded H-tier boundary satisfaction”.
  --
  -- We deliberately define `Sat_R` using `Sat_H_bnd` because:
  -- - it is world-indexed via `to∂ : Cosp → ∂Cosp`,
  -- - it is already connected to the canonical H-layer via `sat-coh`.

  Sat_R : Cosp → Kernel.Code K → Set ℓ
  Sat_R w γ = Kernel.Sat_H_bnd K (to∂ w) (Kernel.decode K γ)

  -- H↔R coherence: H-satisfaction at `decode γ` matches the R-tier definition.
  coh-HR
    : ∀ (w : Cosp) (γ : Kernel.Code K)
    → Prop._↔_
        (HT.HLayer.Sat_H (Kernel.HTruth K) w (Kernel.decode K γ))
        (Sat_R w γ)
  coh-HR w γ = Kernel.sat-coh K w (Kernel.decode K γ)

  -- S↔R coherence (via H): strict truth of φ matches decoded truth of its image in code.
  --
  -- We keep this in preorder-safe form (logical equivalence `_↔_`), avoiding any
  -- extensional equality between predicates.

  codeOfFml : Kernel.Fml K → Kernel.Code K
  codeOfFml φ = Kernel.encode K (Kernel.TransH K φ)

  decode-codeOfFml : ∀ φ → Kernel.decode K (codeOfFml φ) ≡ Kernel.TransH K φ
  decode-codeOfFml φ = Kernel.decode∘encode K (Kernel.TransH K φ)

  coh-SR
    : ∀ (w : Cosp) (φ : Kernel.Fml K)
    → Prop._↔_
        (ST.StrictLayer.Sat_S (Kernel.Strict K) w φ)
        (Sat_R w (codeOfFml φ))
  coh-SR w φ =
    let
      -- S↔H at TransH φ:
      cohSH = Kernel.coh-LH K w φ
      -- Decode equality: `decode (encode (TransH φ)) ≡ TransH φ`.
      eq = decode-codeOfFml φ

      -- H↔R at the decoded constraint of `codeOfFml φ` (no rewriting needed on the R-side).
      cohHR = Kernel.sat-coh K w (Kernel.decode K (codeOfFml φ))
      eq≈ = ≡→≈CP {CP = BulkBoundary.bnd (Kernel.BB K)} eq

      module H = HT.HLayer (Kernel.HTruth K)
    in
    Prop.intro
      (λ satS →
        Prop.to cohHR
          (H.mono-Con (≈CP⇐ {CP = CPᴴ} eq≈) (Prop.to cohSH satS)))
      (λ satR →
        Prop.from cohSH
          (H.mono-Con (≈CP⇒ {CP = CPᴴ} eq≈) (Prop.from cohHR satR)))

  -- R-tier inherits H-tier monotonicity via `Sat_H_bnd`.
  Sat_R-mono
    : ∀ {w γ δ}
    → Core.Code≤ (Kernel.shape K) γ δ
    → Sat_R w γ
    → Sat_R w δ
  Sat_R-mono {w} {γ} {δ} le sat =
    Core.Sat_H_bnd-mono (Kernel.shape K) le sat

  Sat_R-mono-ctx
    : ∀ {w w' γ}
    → Worlds.WorldH._≤ctx_ (Kernel.HWorld K) w w'
    → Sat_R w γ
    → Sat_R w' γ
  Sat_R-mono-ctx {w} {w'} {γ} w≤w' sat =
    Core.Sat_H_bnd-mono-ctx (Kernel.shape K) w≤w' sat

  -- ------------------------------------------------------------------------
  -- G↔R alignment: `Guard` internalises the step-grade flow at decode level.
  --
  -- This is the kernel’s key “self-execution” coherence.

  decode-Guard
    : ∀ γ → Kernel.decode K (Kernel.Guard K γ)
          ≡ GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
              (Kernel.decode K γ)
  decode-Guard = Kernel.guard-decode K

  decode-FlowCode-step
    : ∀ γ → Kernel.decode K (FlowCode K γ)
          ≡ GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
              (Kernel.Body∂ K (Kernel.decode K γ))
  decode-FlowCode-step γ = LogOS.Kernel.decode-FlowCode K γ

  -- Distinguished fixed-point witness lines up at the reflection boundary.
  decode-γ*-is-Th*
    : Kernel.decode K (Kernel.γ* K) ≡ GTier.Th* (Kernel.G K)
  decode-γ*-is-Th* = Kernel.decode-γ* K

  -- ------------------------------------------------------------------------
  -- R-tier stability under the guarded step (explicit boundary view).
  --
  -- These lemmas make the “guarded truth” story concrete: satisfaction at the
  -- reflection layer after Guard/FlowCode is equivalent to satisfaction at the
  -- decoded guarded boundary constraint.

  Sat_R-Guard
    : ∀ (w : Cosp) (γ : Kernel.Code K)
    → Prop._↔_
        (Sat_R w (Kernel.Guard K γ))
        (Kernel.Sat_H_bnd K (to∂ w)
          (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
            (Kernel.decode K γ)))
  Sat_R-Guard w γ =
    let
      eq = decode-Guard γ
      eq≈ = ≡→≈CP {CP = BulkBoundary.bnd (Kernel.BB K)} eq
    in
    Prop.intro
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇒ {CP = CPᴴ} eq≈) sat)
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇐ {CP = CPᴴ} eq≈) sat)

  Sat_R-FlowCode
    : ∀ (w : Cosp) (γ : Kernel.Code K)
    → Prop._↔_
        (Sat_R w (FlowCode K γ))
        (Kernel.Sat_H_bnd K (to∂ w)
          (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
            (Kernel.Body∂ K (Kernel.decode K γ))))
  Sat_R-FlowCode w γ =
    let
      eq = decode-FlowCode-step γ
      eq≈ = ≡→≈CP {CP = BulkBoundary.bnd (Kernel.BB K)} eq
    in
    Prop.intro
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇒ {CP = CPᴴ} eq≈) sat)
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇐ {CP = CPᴴ} eq≈) sat)

  Sat_R-BoxAt
    : ∀ (w : Cosp)
      (g : GTier.Step (Kernel.G K))
      (γ : Kernel.Code K)
    → Prop._↔_
        (Sat_R w (BoxAt K g γ))
        (Kernel.Sat_H_bnd K (to∂ w)
          (GTier.Flow (Kernel.G K) g (Kernel.decode K γ)))
  Sat_R-BoxAt w g γ =
    let
      eq = decode-BoxAt K g γ
      eq≈ = ≡→≈CP {CP = BulkBoundary.bnd (Kernel.BB K)} eq
    in
    Prop.intro
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇒ {CP = CPᴴ} eq≈) sat)
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇐ {CP = CPᴴ} eq≈) sat)

  Sat_R-Box
    : ∀ (w : Cosp) (γ : Kernel.Code K)
    → Prop._↔_
        (Sat_R w (Box K γ))
        (Kernel.Sat_H_bnd K (to∂ w)
          (GTier.Flow (Kernel.G K) (GTier.sat (Kernel.G K))
            (Kernel.decode K γ)))
  Sat_R-Box w γ =
    Sat_R-BoxAt w (GTier.sat (Kernel.G K)) γ

  Sat_R-γ*
    : ∀ (w : Cosp)
    → Prop._↔_
        (Sat_R w (Kernel.γ* K))
        (Kernel.Sat_H_bnd K (to∂ w) (GTier.Th* (Kernel.G K)))
  Sat_R-γ* w =
    let
      eq = decode-γ*-is-Th*
      eq≈ = ≡→≈CP {CP = BulkBoundary.bnd (Kernel.BB K)} eq
    in
    Prop.intro
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇒ {CP = CPᴴ} eq≈) sat)
      (λ sat → Core.Sat_H_bnd-mono (Kernel.shape K) (≈CP⇐ {CP = CPᴴ} eq≈) sat)
