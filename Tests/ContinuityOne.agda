{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.ContinuityOne where

open import LogOS.Prelude

open import LogOS.API.Minimal
open import LogOS.Minimal.Truth as Truth

-- One-point boundary poset and trivial structures

data One : Set where • : One

infix 4 _≤₁_

_≤₁_ : One → One → Set
_≤₁_ _ _ = ⊤

refl₁ : ∀ {x} → _≤₁_ x x
refl₁ = tt

trans₁ : ∀ {x y z} → _≤₁_ x y → _≤₁_ y z → _≤₁_ x z
trans₁ _ _ = tt

ConPoset₁ : ConPoset lzero
ConPoset₁ = record { Con = One ; _⊑_ = λ _ _ → ⊤ ; refl = tt ; trans = λ _ _ → tt }

BB₁ : BulkBoundary lzero
BB₁ = record { bulk = ConPoset₁ ; bnd = ConPoset₁ }

-- Minimal signature/adapter/world for a kernel over One

Sig₁ : LogOSSignature lzero
Sig₁ = record
  { sorts = record { Iface = ⊤ ; Cosp = ⊤ ; ∂Cosp = ⊤ }
  ; cospanOps = record { src = λ _ → tt ; tgt = λ _ → tt ; idC = λ _ → tt ; _∘C_ = λ _ _ → tt ; _⊕C_ = λ _ _ → tt ; _⊗C_ = λ _ _ → tt }
  ; boundaryOps = record { src∂ = λ _ → tt ; tgt∂ = λ _ → tt ; id∂ = λ _ → tt ; _∘∂_ = λ _ _ → tt ; _⊕∂_ = λ _ _ → tt ; _⊗∂_ = λ _ _ → tt ; from∂ = λ _ → tt ; to∂ = λ _ → tt }
  }

Q₁ : QAdapter lzero
Q₁ = trivialQAdapter

module W₁ = Worlds Sig₁

HWorld₁ : W₁.WorldH Q₁
HWorld₁ = record { _≤ctx_ = λ _ _ → ⊤ ; WFlow = λ _ _ → tt ; wflow-refl = λ _ → tt ; wflow-trans = λ _ _ _ → tt }

-- Trivial guarded closure, ω-CPO, and finite-first structure
module GT₁ = Truth.GuardedTruth Sig₁ Q₁

GTruth₁ : GT₁.GuardedClosure (BulkBoundary.bnd BB₁)
GTruth₁ = record
  { Flow      = λ _ → •
  ; mono      = λ _ → tt
  ; infl      = λ _ → tt
  ; idemp-lax = λ _ → tt
  ; Th*       = •
  ; Th*-fixed = (tt , tt)
  }

OmegaCPO₁ : GT₁.OmegaCPO (BulkBoundary.bnd BB₁)
OmegaCPO₁ = record
  { ⊥ = •
  ; isBot = λ _ → tt
  ; supω = λ _ → •
  ; ub    = λ _ _ → tt
  ; least = λ _ _ _ → tt
  }

FiniteFirst₁ : GT₁.FiniteFirst (BulkBoundary.bnd BB₁) GTruth₁ OmegaCPO₁
FiniteFirst₁ = record
  { approx0 = •
  ; approxS = λ _ → •
  ; base = refl
  ; step = λ _ → refl
  ; Th⋆-as-sup = (tt , tt)
  ; cont-ω = λ _ _ → tt
  }

-- Minimal kernel over One
K₁ : Kernel Sig₁ Q₁
K₁ = record
  { shape = record
      { HWorld = HWorld₁
      ; BB = BB₁
      ; MBulk = record { _⊗_ = λ x _ → x ; I = • ; mono⊗ = λ _ _ → tt }
      ; MBnd = record { _⊗_ = λ x _ → x ; I = • ; mono⊗ = λ _ _ → tt }
      ; Holo = record
          { core = record
              { ext = λ x → x
              ; bnd = λ x → x
              ; unit-lax = λ _ → tt
              ; counit-lax = λ _ → tt
              }
          ; ext-⊗-lax = λ _ _ → tt
          ; ext-I-lax = tt
          ; bnd-⊗-lax = λ _ _ → tt
          ; bnd-I-lax = tt
          }
      ; HTruth = record { Sat_H = λ _ _ → ⊤ ; mono-Con = λ _ _ → tt ; mono-ctx = λ _ _ → tt }
      ; HInv = record { Inv_H = λ c → c ; infl = λ _ → tt ; idemp-lax = λ _ → tt }
      ; Sat_H_bnd = λ _ _ → ⊤
      ; sat-coh = λ _ _ → record { to = λ x → x ; from = λ x → x }
      ; Fml = ⊤
      ; Strict = record { Sat_S = λ _ _ → ⊤ }
      ; TransH = λ _ → •
      ; coh-LH = λ _ _ → record { to = λ x → x ; from = λ x → x }
      ; Code = One
      ; encode = λ c → c
      ; decode = λ γ → γ
      ; Guard = λ _ → •
      ; Body = λ γ → γ
      ; γ* = •
      ; reify = λ γ → γ
      ; Body∂ = λ c → c
      }
  ; GTruth = GTruth₁
  ; laws = record
      { shapeLaws = record
          { decode∘encode = λ _ → refl
          ; γ*-guard = (tt , tt)
          ; reify-decode = λ _ → refl
          ; body-decode = λ _ → refl
          }
      ; mono-Body∂ = λ _ → tt
      ; mono-Flow = λ _ → tt
      ; guard-decode = λ _ → refl
      ; decode-γ* = refl
      }
  }
