{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.InterlinguaMuNontrivial where

-- Smoke test: instantiate μ-level interlingua transport (via the
-- interoperability spine) on a nontrivial ωCPO.
--
-- We use a standard ωCPO of predicates (pointwise implication, ω-sup = union),
-- so the constraint preorder is not the top preorder.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥; ⊥-elim; ↔-refl)

open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; satSystem; PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Theorems.Boundary.OmegaCPOMapKit as OmegaKit

open import LogOS.Prelude using (ℕ; zero; suc)

-- Context is irrelevant here.
Ctx : Set lzero
Ctx = ⊤ {ℓ = lzero}

-- Constraints: predicates over ℕ.
Con : Set (lsuc lzero)
Con = ℕ → Set lzero

-- Pointwise implication preorder on predicates.
CPPred : ConPreorder (lsuc lzero)
CPPred =
  record
    { Con = Con
    ; _⊑_ = λ P Q → Lift (lsuc lzero) (∀ i → P i → Q i)
    ; refl = lift (λ _ p → p)
    ; trans = λ PQ QR → lift (λ i p → lower QR i (lower PQ i p))
    }

-- ωCPO structure: ⊥ = empty predicate, supω = union of the chain.
ωPred : Truth.GuardedCore.OmegaCPO CPPred
ωPred =
  record
    { ⊥ = λ _ → ⊥
    ; isBot = λ _ → lift (λ _ bot → ⊥-elim bot)
    ; supω = λ f i → Σ ℕ (λ n → f n i)
    ; ub = λ _ n → lift (λ i p → n , p)
    ; least = λ _ X ubf → lift (λ i w → lower (ubf (proj₁ w)) i (proj₂ w))
    }

-- A nontrivial `SatMor`: shift constraints, and shift the observer index.
shift : Con → Con
shift P i = P (suc i)

Sat₁ : Ctx → Con → Set lzero
Sat₁ _ P = P (suc zero)

Sat₂ : Ctx → Con → Set lzero
Sat₂ _ P = P zero

S₁ : SatSystem {ℓCtx = lzero} {ℓCon = lsuc lzero} {ℓSat = lzero}
S₁ = satSystem Ctx Con Sat₁

S₂ : SatSystem {ℓCtx = lzero} {ℓCon = lsuc lzero} {ℓSat = lzero}
S₂ = satSystem Ctx Con Sat₂

m : SatMor S₁ S₂
m =
  record
    { mapCtx = λ p → p
    ; mapCon = shift
    ; sat-↔  = λ _ _ → ↔-refl
    }

-- Identity presentation (Form = Con).
P₁ : PresentationC {ℓForm = lsuc lzero} S₁
P₁ =
  record
    { Form = Con
    ; SatF = Sat₁
    ; Export = λ c → c
    ; SatC≈F = λ _ _ → ↔-refl
    ; Import = λ φ → φ
    ; SatF≈C = λ _ _ → ↔-refl
    }

P₂ : PresentationC {ℓForm = lsuc lzero} S₂
P₂ =
  record
    { Form = Con
    ; SatF = Sat₂
    ; Export = λ c → c
    ; SatC≈F = λ _ _ → ↔-refl
    ; Import = λ φ → φ
    ; SatF≈C = λ _ _ → ↔-refl
    }

module L = Interop.Limit CPPred CPPred m P₁ P₂

-- ωCPO-map structure for `shift`.
module OK = OmegaKit.For CPPred CPPred

shiftΩ : OK.OmegaCPOMap ωPred ωPred shift
shiftΩ =
  record
    { mono-map = λ PQ → lift (λ i p → lower PQ (suc i) p)
    ; strict⊥  = ConPreorder.refl CPPred
    ; cont-ω   = λ _ _ → ConPreorder.refl CPPred
    }

-- A simple, inflationary, monotone operator on predicates that commutes with `shift`.
F : Con → Con
F P i = P i ⊎ P (suc i)

monoF : ∀ {P Q} → ConPreorder._⊑_ CPPred P Q → ConPreorder._⊑_ CPPred (F P) (F Q)
monoF PQ =
  lift (λ i → λ where
    (inj₁ p) → inj₁ (lower PQ i p)
    (inj₂ p) → inj₂ (lower PQ (suc i) p))

inflF : ∀ P → ConPreorder._⊑_ CPPred P (F P)
inflF _ = lift (λ _ p → inj₁ p)

transportData : L.MuTransportData ωPred ωPred F F
transportData =
  record
    { Mω = shiftΩ
    ; monoF₂ = monoF
    ; inflF₁ = inflF
    ; comm = λ _ → ConPreorder.refl CPPred
    ; monoSat₂ = λ {p} {c} {d} cd sat → lower cd zero sat
    }

μF : Con
μF = Truth.GuardedCore.Kleene.μ ωPred F

-- Concrete instance: the μ-level interlingua transport specialises to “μF 1 → μF 0”.
transport-ok : μF (suc zero) → μF zero
transport-ok prem = L.translate-μ≤ transportData tt prem
