{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Opacity.Demo where

-- Minimal single-view opacity slice.
-- code carries an intensional tag that is *not observable* at the boundary.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; refl⊑)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode; CodePreorder)
open import LogOS.LT.Hom using (KernelHom; mkKernelHomParts; _⇒_)
open import LogOS.Ports.IO using (IOPort)
import LogOS.Ports.Opacity.Port as Opacity
open import LogOS.Ports.Opacity.Port.Definitional using (_≃obs_)
open Opacity
open import LogOS.Ports.Universality.NatBoundary using (NatBoundary)

-- Boundary preorder: Nat budget/fuel order.
--
-- Note: strict observational equality (`≃`) remains *propositional equality*
-- pulled back along the view; the boundary preorder is only used for `_⊑_`/`≈`.
Nat : ConPreorder lzero lzero
Nat = NatBoundary

-- A kernel where `Code = ℕ × ℕ`, but `decode` forgets the second component.
-- The second component is an intensional “tag”; it is opaque at the boundary.

K : Kernel lzero lzero lzero
K =
  record
    { bnd = Nat
    ; Code = ℕ × ℕ
    ; decode = fst
    }

-- Opacity port: the observation boundary for code is `decode`.
codeOpacity : OpacityPort (Code K) (bnd K)
codeOpacity = record { observe = record { μ = decode K } }

open OpacityPort codeOpacity
-- Tags are invisible at the boundary (strict observation equality).
tag-opaque≃
  : ∀ (n t₁ t₂ : ℕ) → _≃obs_ codeOpacity (n , t₁) (n , t₂)
tag-opaque≃ n t₁ t₂ = refl

-- Same statement as refinement in the induced code preorder.
tag-opaque⊑
  : ∀ (n t₁ t₂ : ℕ) → _⊑_ (CodePreorder K) (n , t₁) (n , t₂)
tag-opaque⊑ n t₁ t₂ = refl⊑ Nat

codeTelemetry : IOPort (Code K) ⊤ (bnd K)
codeTelemetry = opacityIOPort codeOpacity

open IOPort codeTelemetry using (_⊑io_)

tag-opaque⊑io
  : ∀ (n t₁ t₂ : ℕ) → (n , t₁) ⊑io (n , t₂)
tag-opaque⊑io n t₁ t₂ _ _ = refl⊑ Nat

-- Two different implementations behind the same boundary:
-- - `idTag` keeps the tag
-- - `eraseTag` erases the tag
--
-- They are mutually refining under the implementation-first refinement `_⇒_` (pullback along `obsView`).
-- Base `LOG` uses the boundary-driven refinement `_⇒∂_`, which is equivalent via `decode-mapCode`.

idTag : KernelHom K K
idTag =
  mkKernelHomParts
    (record
      { map∂ = λ c → c
      ; map∂-mono = λ le → le
      })
    (record
      { mapCode = λ γ → γ
      ; decode-mapCode = λ _ → (refl⊑ Nat , refl⊑ Nat)
      })

eraseTag : KernelHom K K
eraseTag =
  mkKernelHomParts
    (record
      { map∂ = λ c → c
      ; map∂-mono = λ le → le
      })
    (record
      { mapCode = λ γ → (fst γ , zero)
      ; decode-mapCode = λ _ → (refl⊑ Nat , refl⊑ Nat)
      })

idTag⇒eraseTag : idTag ⇒ eraseTag
idTag⇒eraseTag _ = refl⊑ Nat

eraseTag⇒idTag : eraseTag ⇒ idTag
eraseTag⇒idTag _ = refl⊑ Nat
