{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.HP.Flow where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import LogOS.Computation.Core using (iterateStep)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.TensorDSL

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface

-- Transport facts between boundary Flow and an abstract operator Op via an embed.

Flow-fixed→Op-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
  → ∀ c
  → (Endo.fn (Flow-Endo K) c ≡ c)
  → HPInterface.Op HP (HPInterface.embed HP c) ≡ HPInterface.embed HP c
Flow-fixed→Op-fixed K HP c flow-fixed =
  let E = HPInterface.embed HP in
  trans (sym (HPInterface.intertwine HP c)) (cong E flow-fixed)

Op-fixed→Flow-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
    (EF : EmbedFaithful K HP)
  → ∀ c
  → (HPInterface.Op HP (HPInterface.embed HP c) ≡ HPInterface.embed HP c)
  → Endo.fn (Flow-Endo K) c ≡ c
Op-fixed→Flow-fixed K HP EF c op-fixed =
  EmbedFaithful.embed-reflects≡ EF (trans (HPInterface.intertwine HP c) op-fixed)

-- Bi-implication and n-step intertwining.

Flow-fixed↔Op-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
    (EF : EmbedFaithful K HP)
  → ∀ c →
    (Endo.fn (Flow-Endo K) c ≡ c)
    ↔ (HPInterface.Op HP (HPInterface.embed HP c) ≡ HPInterface.embed HP c)
Flow-fixed↔Op-fixed K HP EF c =
  intro
    (λ tf → Flow-fixed→Op-fixed K HP c tf)
    (λ op → Op-fixed→Flow-fixed K HP EF c op)

intertwine-iter
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
  → ∀ n c →
      HPInterface.embed HP (iterateStep (Endo.fn (Flow-Endo K)) n c)
      ≡ iterateStep (HPInterface.Op HP) n (HPInterface.embed HP c)
intertwine-iter K HP zero    c = refl
intertwine-iter K HP (suc n) c =
  let F = Endo.fn (Flow-Endo K)
      O = HPInterface.Op HP
      E = HPInterface.embed HP
  in
  trans (intertwine-iter K HP n (F c))
       (cong (iterateStep O n) (HPInterface.intertwine HP c))

Opⁿ-fixed→Flowⁿ-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
    (EF : EmbedFaithful K HP)
  → ∀ n c →
      iterateStep (HPInterface.Op HP) n (HPInterface.embed HP c) ≡ HPInterface.embed HP c
      → iterateStep (Endo.fn (Flow-Endo K)) n c ≡ c
Opⁿ-fixed→Flowⁿ-fixed K HP EF n c opⁿ =
  let E = HPInterface.embed HP in
  EmbedFaithful.embed-reflects≡ EF (trans (intertwine-iter K HP n c) opⁿ)


Flowⁿ-fixed→Opⁿ-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
  → ∀ n c →
      iterateStep (Endo.fn (Flow-Endo K)) n c ≡ c
      → iterateStep (HPInterface.Op HP) n (HPInterface.embed HP c) ≡ HPInterface.embed HP c
Flowⁿ-fixed→Opⁿ-fixed K HP n c tfⁿ =
  let E = HPInterface.embed HP in
  trans (sym (intertwine-iter K HP n c)) (cong E tfⁿ)

Flowⁿ-fixed↔Opⁿ-fixed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (HP : HPInterface K)
    (EF : EmbedFaithful K HP)
  → ∀ n c →
      (iterateStep (Endo.fn (Flow-Endo K)) n c ≡ c)
      ↔ (iterateStep (HPInterface.Op HP) n (HPInterface.embed HP c) ≡ HPInterface.embed HP c)
Flowⁿ-fixed↔Opⁿ-fixed K HP EF n c =
  intro
    (λ tfⁿ → Flowⁿ-fixed→Opⁿ-fixed K HP n c tfⁿ)
    (λ opⁿ → Opⁿ-fixed→Flowⁿ-fixed K HP EF n c opⁿ)
