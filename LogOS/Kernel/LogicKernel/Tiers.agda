{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Tiers where

-- ============================================================================
-- S/H/G/R TIER ALIGNMENT (DERIVED INTERFACE)
--
-- This module makes the “four tiers” explicit for any `LogicKernel`:
-- - S-tier: strict satisfaction `Sat_S`
-- - H-tier: homotypical satisfaction `Sat_H` and boundary satisfaction `Sat_H_bnd`
-- - G-tier: guarded flow `Flow` and distinguished fixed point `Th*`
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
open import LogOS.Syntax.Prop as Prop

open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.Core as Core hiding (FlowCode)

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LogicKernel Sig Q)
  where
  open LogOSSignature Sig
  module ST = Truth.StrictTruth Sig
  module HT = Truth.HomotypicalTruth Sig Q (LogicKernel.HWorld K)

  -- ------------------------------------------------------------------------
  -- R-tier (reflection) as “decoded H-tier boundary satisfaction”.
  --
  -- We deliberately define `Sat_R` using `Sat_H_bnd` because:
  -- - it is world-indexed via `to∂ : Cosp → ∂Cosp`,
  -- - it is already connected to the canonical H-layer via `sat-coh`.

  Sat_R : Cosp → LogicKernel.Code K → Set ℓ
  Sat_R w γ = LogicKernel.Sat_H_bnd K (to∂ w) (LogicKernel.decode K γ)

  -- H↔R coherence: H-satisfaction at `decode γ` matches the R-tier definition.
  coh-HR
    : ∀ (w : Cosp) (γ : LogicKernel.Code K)
    → Prop._↔_
        (HT.HLayer.Sat_H (LogicKernel.HTruth K) w (LogicKernel.decode K γ))
        (Sat_R w γ)
  coh-HR w γ = LogicKernel.sat-coh K w (LogicKernel.decode K γ)

  -- S↔R coherence (via H): strict truth of φ matches decoded truth of its image in code.
  --
  -- We keep this in preorder-safe form (logical equivalence `_↔_`), avoiding any
  -- extensional equality between predicates.

  codeOfFml : LogicKernel.Fml K → LogicKernel.Code K
  codeOfFml φ = LogicKernel.encode K (LogicKernel.TransH K φ)

  decode-codeOfFml : ∀ φ → LogicKernel.decode K (codeOfFml φ) ≡ LogicKernel.TransH K φ
  decode-codeOfFml φ = LogicKernel.decode∘encode K (LogicKernel.TransH K φ)

  coh-SR
    : ∀ (w : Cosp) (φ : LogicKernel.Fml K)
    → Prop._↔_
        (ST.StrictLayer.Sat_S (LogicKernel.Strict K) w φ)
        (Sat_R w (codeOfFml φ))
  coh-SR w φ =
    let
      -- S↔H at TransH φ:
      cohSH = LogicKernel.coh-LH K w φ
      -- Decode equality: `decode (encode (TransH φ)) ≡ TransH φ`.
      eq = decode-codeOfFml φ

      -- H↔R at the decoded constraint of `codeOfFml φ` (no rewriting needed on the R-side).
      cohHR = LogicKernel.sat-coh K w (LogicKernel.decode K (codeOfFml φ))
    in
    Prop.intro
      (λ satS →
        Prop.to cohHR
          (subst (λ c → HT.HLayer.Sat_H (LogicKernel.HTruth K) w c) (sym eq)
            (Prop.to cohSH satS)))
      (λ satR →
        Prop.from cohSH
          (subst (λ c → HT.HLayer.Sat_H (LogicKernel.HTruth K) w c) eq
            (Prop.from cohHR satR)))

  -- R-tier inherits H-tier monotonicity via `Sat_H_bnd`.
  Sat_R-mono
    : ∀ {w γ δ}
    → Core.Code≤ (LogicKernel.shape K) γ δ
    → Sat_R w γ
    → Sat_R w δ
  Sat_R-mono {w} {γ} {δ} le sat =
    Core.Sat_H_bnd-mono (LogicKernel.shape K) le sat

  Sat_R-mono-ctx
    : ∀ {w w' γ}
    → Worlds.WorldH._≤ctx_ (LogicKernel.HWorld K) w w'
    → Sat_R w γ
    → Sat_R w' γ
  Sat_R-mono-ctx {w} {w'} {γ} w≤w' sat =
    Core.Sat_H_bnd-mono-ctx (LogicKernel.shape K) w≤w' sat

  -- ------------------------------------------------------------------------
  -- G↔R alignment: `Guard` internalises the step-grade flow at decode level.
  --
  -- This is the kernel’s key “self-execution” coherence.

  decode-Guard
    : ∀ γ → LogicKernel.decode K (LogicKernel.Guard K γ)
          ≡ GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K))
              (LogicKernel.decode K γ)
  decode-Guard = LogicKernel.guard-decode K

  decode-FlowCode-step
    : ∀ γ → LogicKernel.decode K (FlowCode K γ)
          ≡ GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K))
              (LogicKernel.Body∂ K (LogicKernel.decode K γ))
  decode-FlowCode-step γ = LogOS.Kernel.LogicKernel.decode-FlowCode K γ

  -- Distinguished fixed point lines up at the reflection boundary.
  decode-γ*-is-Th*
    : LogicKernel.decode K (LogicKernel.γ* K) ≡ GTier.Th* (LogicKernel.G K)
  decode-γ*-is-Th* = LogicKernel.decode-γ* K

  -- ------------------------------------------------------------------------
  -- R-tier stability under the guarded step (explicit boundary view).
  --
  -- These lemmas make the “guarded truth” story concrete: satisfaction at the
  -- reflection layer after Guard/FlowCode is equivalent to satisfaction at the
  -- decoded guarded boundary constraint.

  Sat_R-Guard
    : ∀ (w : Cosp) (γ : LogicKernel.Code K)
    → Prop._↔_
        (Sat_R w (LogicKernel.Guard K γ))
        (LogicKernel.Sat_H_bnd K (to∂ w)
          (GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K))
            (LogicKernel.decode K γ)))
  Sat_R-Guard w γ =
    let eq = decode-Guard γ in
    Prop.intro
      (λ sat → subst (λ c → LogicKernel.Sat_H_bnd K (to∂ w) c) eq sat)
      (λ sat → subst (λ c → LogicKernel.Sat_H_bnd K (to∂ w) c) (sym eq) sat)

  Sat_R-FlowCode
    : ∀ (w : Cosp) (γ : LogicKernel.Code K)
    → Prop._↔_
        (Sat_R w (FlowCode K γ))
        (LogicKernel.Sat_H_bnd K (to∂ w)
          (GTier.Flow (LogicKernel.G K) (GTier.step (LogicKernel.G K))
            (LogicKernel.Body∂ K (LogicKernel.decode K γ))))
  Sat_R-FlowCode w γ =
    let eq = decode-FlowCode-step γ in
    Prop.intro
      (λ sat → subst (λ c → LogicKernel.Sat_H_bnd K (to∂ w) c) eq sat)
      (λ sat → subst (λ c → LogicKernel.Sat_H_bnd K (to∂ w) c) (sym eq) sat)

  Sat_R-γ*
    : ∀ (w : Cosp)
    → Prop._↔_
        (Sat_R w (LogicKernel.γ* K))
        (LogicKernel.Sat_H_bnd K (to∂ w) (GTier.Th* (LogicKernel.G K)))
  Sat_R-γ* w =
    let eq = decode-γ*-is-Th* in
    Prop.intro
      (λ sat → subst (λ c → LogicKernel.Sat_H_bnd K (to∂ w) c) eq sat)
      (λ sat → subst (λ c → LogicKernel.Sat_H_bnd K (to∂ w) c) (sym eq) sat)
