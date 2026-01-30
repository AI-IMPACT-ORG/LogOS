{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.DecodeTransportKit where

-- Generic “decode transport” lemmas.
--
-- Purpose: remove boilerplate proofs of the form
--   `decode(map γ₁) ≈ decode(map γ₂)` obtained from
--   `decode γ₁ ≈ decode γ₂` plus “map preserves decode (up to ≈)”.
--
-- This module provides:
-- - Pullback lemmas for decode-extensional predicates and functions.
-- - A stability pullback lemma under step-commutation up to decoded ≈.
-- - A KernelHom-specific helper for transporting strict decode equalities.

open import LogOS.Prelude

open import LogOS.Syntax.Prop using (↔-trans)
open import LogOS.Minimal.Con using (ConPreorder; _≈CP_; ≈CP-trans; ≈CP-sym)
import LogOS.Theorems.Meta.ObserverCore as ObsCore

-- Pullback of decode-extensionality (≈) along a decode-preserving map.
pullback-DecodeExtensional≈
  : ∀ {ℓCode₁ ℓCode₂ ℓDec ℓP : Level}
    {Code₁ : Set ℓCode₁} {Code₂ : Set ℓCode₂}
    (CP : ConPreorder ℓDec)
    (decode₁ : Code₁ → ConPreorder.Con CP)
    (decode₂ : Code₂ → ConPreorder.Con CP)
    (map : Code₁ → Code₂)
    (map-decode≈ : ∀ γ → _≈CP_ CP (decode₂ (map γ)) (decode₁ γ))
    (P₂ : Code₂ → Set ℓP)
  → ObsCore.DecodeExtensional≈ CP decode₂ P₂
  → ObsCore.DecodeExtensional≈ CP decode₁ (λ γ → P₂ (map γ))
pullback-DecodeExtensional≈ CP decode₁ decode₂ map map-decode≈ P₂ ext₂ γ₁ γ₂ eq p =
  let
    eq₁ : _≈CP_ CP (decode₂ (map γ₁)) (decode₁ γ₁)
    eq₁ = map-decode≈ γ₁

    eq₂ : _≈CP_ CP (decode₂ (map γ₂)) (decode₁ γ₂)
    eq₂ = map-decode≈ γ₂

    eqmap : _≈CP_ CP (decode₂ (map γ₁)) (decode₂ (map γ₂))
    eqmap = ≈CP-trans {CP = CP} eq₁ (≈CP-trans {CP = CP} eq (≈CP-sym {CP = CP} eq₂))
  in
  ext₂ _ _ eqmap p

-- Function-specialised pullback: decode-extensionality (≈) for `f : Code → X`.
pullback-DecodeExtensionalFn≈
  : ∀ {ℓCode₁ ℓCode₂ ℓDec ℓX : Level}
    {Code₁ : Set ℓCode₁} {Code₂ : Set ℓCode₂}
    (CP : ConPreorder ℓDec)
    (decode₁ : Code₁ → ConPreorder.Con CP)
    (decode₂ : Code₂ → ConPreorder.Con CP)
    (map : Code₁ → Code₂)
    (map-decode≈ : ∀ γ → _≈CP_ CP (decode₂ (map γ)) (decode₁ γ))
    {X : Set ℓX}
    (f : Code₂ → X)
  → (∀ γ₁ γ₂ → _≈CP_ CP (decode₂ γ₁) (decode₂ γ₂) → f γ₁ ≡ f γ₂)
  → (∀ γ₁ γ₂ → _≈CP_ CP (decode₁ γ₁) (decode₁ γ₂) → f (map γ₁) ≡ f (map γ₂))
pullback-DecodeExtensionalFn≈ CP decode₁ decode₂ map map-decode≈ f ext₂ γ₁ γ₂ eq =
  let
    eq₁ = map-decode≈ γ₁
    eq₂ = map-decode≈ γ₂
    eqmap = ≈CP-trans {CP = CP} eq₁ (≈CP-trans {CP = CP} eq (≈CP-sym {CP = CP} eq₂))
  in
  ext₂ _ _ eqmap

-- Pullback of stability along a map when `map` commutes with `step` up to decoded ≈.
--
-- If P₂ is decode-extensional (≈) and stable under `step₂`,
-- and `decode₂ (step₂ (map γ)) ≈ decode₂ (map (step₁ γ))`,
-- then `P₂ ∘ map` is stable under `step₁`.
pullback-StableUnder≈
  : ∀ {ℓCode₁ ℓCode₂ ℓDec ℓP : Level}
    {Code₁ : Set ℓCode₁} {Code₂ : Set ℓCode₂}
    (CP : ConPreorder ℓDec)
    (decode₂ : Code₂ → ConPreorder.Con CP)
    (map : Code₁ → Code₂)
    (step₁ : Code₁ → Code₁)
    (step₂ : Code₂ → Code₂)
    (P₂ : Code₂ → Set ℓP)
  → (∀ γ → _≈CP_ CP (decode₂ (step₂ (map γ))) (decode₂ (map (step₁ γ))))
  → ObsCore.DecodeExtensional≈ CP decode₂ P₂
  → ObsCore.StableUnder step₂ P₂
  → ObsCore.StableUnder step₁ (λ γ → P₂ (map γ))
pullback-StableUnder≈ CP decode₂ map step₁ step₂ P₂ eqStep ext₂ stable₂ γ =
  ↔-trans
    (stable₂ (map γ))
    (ObsCore.DecodeExtensional≈-cong {CP = CP} {decode = decode₂} {P = P₂} ext₂ (eqStep γ))

-- --------------------------------------------------------------------------
-- KernelHom specialisation: strict decode equality transport.
-- --------------------------------------------------------------------------

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Algebra.ConAlg using (ConAlgHom≡)
open import LogOS.Syntax.Eq using (module ForKernel)

-- If two source codes have equal decoded boundary meaning, then mapping them
-- along a kernel hom yields equal decoded boundary meaning at the target.
decode-mapCode-cong
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    {γ₁ γ₂ : Kernel.Code K₁}
  → Kernel.decode K₁ γ₁ ≡ Kernel.decode K₁ γ₂
  → Kernel.decode K₂ (KernelHom.mapCode h γ₁) ≡ Kernel.decode K₂ (KernelHom.mapCode h γ₂)
decode-mapCode-cong {K₁ = K₁} {K₂ = K₂} h {γ₁ = γ₁} {γ₂ = γ₂} eq =
  trans (KernelHom.map-decode h γ₁)
    (trans (cong (ConAlgHom≡.map∂ (KernelHom.con-hom h)) eq)
      (sym (KernelHom.map-decode h γ₂)))

-- Convenience: turn a source decode equality into target decoded mutual refinement.
mapCode≈K-from-decode≡
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    {γ₁ γ₂ : Kernel.Code K₁}
  → Kernel.decode K₁ γ₁ ≡ Kernel.decode K₁ γ₂
  → ForKernel._≈K_ K₂ (KernelHom.mapCode h γ₁) (KernelHom.mapCode h γ₂)
mapCode≈K-from-decode≡ {K₂ = K₂} h eq =
  let open ForKernel K₂ in
  ≃K→≈K (decode-mapCode-cong h eq)
