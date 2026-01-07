{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Core where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

-- Shared kernel “shape”: everything that is common to ungraded and graded kernels,
-- i.e. the S/H tiers + boundary constraint structure + reflective code interface.
--
-- The guarded (G) tier differs: ungraded kernels use a single closure `Flow : Con → Con`,
-- while graded kernels use a grade-indexed flow `Flow : Grade → Con → Con` and must make
-- the step-grade vs saturation-grade split explicit.

record KernelShape {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  module W = Worlds Sig
  open Truth.StrictTruth Sig

  field
    -- H-tier: world context + Q-weighted flow
    HWorld : W.WorldH Q

  private
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  field
    -- Constraints and lax monoidal adjunction
    BB     : BulkBoundary ℓ
    MBulk  : MonoidalPoset (BulkBoundary.bulk BB)
    MBnd   : MonoidalPoset (BulkBoundary.bnd  BB)
    Holo   : LaxMonoidalAdjunction BB MBulk MBnd

    -- H-tier satisfaction and invariance (dependent on the chosen world)
    HTruth : HT.HLayer BB
    HInv   : HT.Invariance BB

    -- Boundary satisfaction + coherence (optional, internalized)
    Sat_H_bnd : ∂Cosp → (ConPoset.Con (BulkBoundary.bnd BB)) → Set ℓ
    sat-coh   : ∀ (w : Cosp) (c : ConPoset.Con (BulkBoundary.bnd BB)) →
                Prop._↔_ (HT.HLayer.Sat_H HTruth w c)
                         (Sat_H_bnd (to∂ w) c)

    -- S-tier: strict logic interface and translation into H-tier constraints
    Fml    : Set ℓ
    Strict : StrictLayer Fml
    TransH : Fml → (ConPoset.Con (BulkBoundary.bnd BB))
    coh-LH : ∀ (w : Cosp) (φ : Fml) →
             Prop._↔_ (StrictLayer.Sat_S Strict w φ)
                      (HT.HLayer.Sat_H HTruth w (TransH φ))

    -- Code layer: guarded reflection and one-step computation core
    Code   : Set ℓ
    encode : (ConPoset.Con (BulkBoundary.bnd BB)) → Code
    decode : Code → (ConPoset.Con (BulkBoundary.bnd BB))
    decode∘encode : ∀ c → decode (encode c) ≡ c

    Guard         : Code → Code
    Body          : Code → Code

    -- Guarded fixpoint witness at the code level.
    γ*            : Code
    γ*-guard      : (ConPoset._⊑_ (BulkBoundary.bnd BB)
                      (decode γ*)
                      (decode (Guard (Body γ*))))
                    × (ConPoset._⊑_ (BulkBoundary.bnd BB)
                        (decode (Guard (Body γ*)))
                        (decode γ*))

    -- Safe self-reflection (observational)
    reify         : Code → Code
    reify-decode  : ∀ γ → decode (reify γ) ≡ decode γ

    -- Boundary view of code body
    Body∂         : (ConPoset.Con (BulkBoundary.bnd BB)) → (ConPoset.Con (BulkBoundary.bnd BB))
    body-decode   : ∀ γ → decode (Body γ) ≡ Body∂ (decode γ)

open KernelShape public

FlowCodeShape
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (S : KernelShape Sig Q)
  → KernelShape.Code S → KernelShape.Code S
FlowCodeShape S γ = KernelShape.Guard S (KernelShape.Body S γ)

record BodyMonotoneShape
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (S : KernelShape Sig Q) : Set (lsuc (lsuc ℓ)) where
  field
    mono-Body∂
      : ∀ {c d}
      → ConPoset._⊑_ (BulkBoundary.bnd (KernelShape.BB S)) c d
      → ConPoset._⊑_ (BulkBoundary.bnd (KernelShape.BB S))
          (KernelShape.Body∂ S c)
          (KernelShape.Body∂ S d)
