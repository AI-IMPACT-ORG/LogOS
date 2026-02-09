{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.InterlinguaMu where

-- Smoke test: instantiate the μ-level port transport lemma via the
-- interoperability spine, in a trivial model.
--
-- Goal: ensure `LogOS.Ports.Semantic.Interoperability.Limit.translate-μ≤`
-- typechecks and its assumptions are consistent with the ωCPO/μ-fusion
-- infrastructure.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; PresentationC)
open import LogOS.Ports.Semantic.SatMor using (idSatMorS)
import LogOS.Ports.Semantic.Interoperability as Interop

import LogOS.Theorems.Boundary.OmegaCPOMapKit as OmegaKit

Ctx₀ : Set lzero
Ctx₀ = ⊤ {ℓ = lzero}

Con₀ : Set lzero
Con₀ = ⊤ {ℓ = lzero}

-- Trivial preorder on ⊤.
CP⊤ : ConPreorder lzero
CP⊤ =
  record
    { Con = Con₀
    ; _⊑_ = λ _ _ → ⊤ {ℓ = lzero}
    ; refl = tt
    ; trans = λ _ _ → tt
    }

ω⊤ : Truth.GuardedCore.OmegaCPO CP⊤
ω⊤ =
  record
    { ⊥ = tt
    ; isBot = λ _ → tt
    ; supω = λ _ → tt
    ; ub = λ _ _ → tt
    ; least = λ _ _ _ → tt
    }

Sat₀ : Ctx₀ → Con₀ → Set lzero
Sat₀ _ _ = ⊤ {ℓ = lzero}

S : SatSystem
S = record { Ctx = Ctx₀ ; Con = Con₀ ; Sat = Sat₀ }

P : PresentationC {ℓCtx = lzero} {ℓCon = lzero} {ℓForm = lzero} {ℓSat = lzero} S
P =
  record
    { Form = Con₀
    ; SatF = Sat₀
    ; Export = λ c → c
    ; SatC≈F = λ _ _ → Prop.↔-refl
    ; Import = λ φ → φ
    ; SatF≈C = λ _ _ → Prop.↔-refl
    }

module L = Interop.Limit CP⊤ CP⊤ idSatMorS P P

F : Con₀ → Con₀
F x = x

inflF : ∀ c → ConPreorder._⊑_ CP⊤ c (F c)
inflF _ = tt

commF : ∀ c → ConPreorder._⊑_ CP⊤ ((λ x → x) (F c)) (F ((λ x → x) c))
commF _ = tt

transportData : L.MuTransportData ω⊤ ω⊤ F F
transportData =
  record
    { Mω = OmegaKit.idOmegaCPOMap CP⊤ {ω = ω⊤}
    ; monoF₂ = λ {c} {d} _ → tt
    ; inflF₁ = inflF
    ; comm = commF
    ; monoSat₂ = λ {p} {c} {d} _ _ → tt
    }

-- The lemma itself: in this trivial setting, it reduces to an identity.
transport-ok : ∀ p → ⊤ {ℓ = lzero} → ⊤ {ℓ = lzero}
transport-ok p = L.translate-μ≤ transportData p
