{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.Pack where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel
import LogOS.Theorems.Meta.ObserverCore as ObsCore
open import LogOS.API.Kernel.Eq using (module ForKernelLike)
open import LogOS.Syntax.Prop using (_↔_; intro; ¬_)
open import LogOS.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)

-- Set-theory packs (full schemata). Canonical entrypoints:
-- - `ZFAxioms` / `ZFCAxioms` here (full Separation/Replacement, meta-level predicates).
-- - `LogOS.ZFC.SetTheory.DefinablePack` for coded/definable schemata.
-- - `LogOS.ZFC.SetTheory.FullUpgradeFromDefinable` to upgrade definable → full.
-- - `LogOS.ZFC.SetTheory.CumulativeSurface.stageToSurface` to obtain a `ZFDsl` from
--   a cumulative hierarchy; use `LogOS.ZFC.SetTheory.LimitPack.toZFAxioms` to recover
--   `ZFAxioms` from the resulting `CumulativeHierarchy`.

record ZFAxioms {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K   : KernelLike Sig Q)
                  : Set (lsuc (lsuc ℓ)) where
  open KernelLike K
  open ForKernelLike K
  field
    SetU   : Set ℓ
    _∈_    : SetU → SetU → Set ℓ

  -- Membership induces an observational preorder on sets (“subset”):
  -- x ⊑ y  :=  ∀ z. z ∈ x → z ∈ y
  infix 4 _∈_ _⊑_ _≈_
  _⊑_ : SetU → SetU → Set ℓ
  x ⊑ y = ∀ z → (z ∈ x) → (z ∈ y)

  -- Extensional equality is mutual refinement in that preorder.
  _≈_ : SetU → SetU → Set ℓ
  x ≈ y = (x ⊑ y) × (y ⊑ x)

  refl≈  : ∀ x → x ≈ x
  refl≈ _ = (λ _ zx → zx) , (λ _ zy → zy)

  sym≈   : ∀ {x y} → x ≈ y → y ≈ x
  sym≈ (xy , yx) = (yx , xy)

  trans≈ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  trans≈ (xy , yx) (yz , zy) =
    ( (λ u ux → yz u (xy u ux))
    , (λ u uz → yx u (zy u uz))
    )

  -- “Presentation layer” (↔) implies extensional equality.
  extensionality : ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≈ y
  extensionality x y hyp =
    ( (λ z exz → _↔_.to (hyp z) exz)
    , (λ z eyz → _↔_.from (hyp z) eyz)
    )

  -- Extensional equality yields pointwise membership equivalence.
  mem-ext : ∀ {x y} → x ≈ y → ∀ z → (z ∈ x) ↔ (z ∈ y)
  mem-ext {x} {y} (xy , yx) z = intro (xy z) (yx z)

  field
    ⟦_⟧     : Code → SetU
    by-decode≈ : ∀ {γ δ} → γ ≃K δ → ⟦ γ ⟧ ≈ ⟦ δ ⟧

    empty : Σ SetU (λ e → ∀ z → ¬ (z ∈ e))
    pairing : ∀ x y → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ ((z ≈ x) ⊎ (z ≈ y)))
    union  : ∀ x → Σ SetU (λ u → ∀ z → (z ∈ u) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y))))
    powerset : ∀ x → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ (∀ w → w ∈ z → w ∈ x))

    zeroS : SetU
    zeroS-empty : ∀ z → ¬ (z ∈ zeroS)
    succ  : SetU → SetU
    mem-succ↔ : ∀ x z → (z ∈ succ x) ↔ ((z ∈ x) ⊎ (z ≈ x))
    infinity : Σ SetU (λ ω → (∀ z → (z ∈ ω) ↔ ((z ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ succ y))))))

    separation : (P : SetU → Set ℓ) → ∀ x → Σ SetU (λ y → ∀ z → (z ∈ y) ↔ ((z ∈ x) × (P z)))
    replacement : (F : SetU → Σ SetU (λ _ → Set ℓ))
                → ∀ x → Σ SetU (λ y → ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → u ∈ x × (proj₁ (F u) ≈ z))))
    foundation : ∀ x → (x ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y))))

  by-decode-ext : ObsCore.DecodeExtensional decode (λ γ → ∀ z → z ∈ ⟦ γ ⟧)
  by-decode-ext γ δ eq d =
    let e : ⟦ γ ⟧ ≈ ⟦ δ ⟧
        e = by-decode≈ eq
    in λ z → _↔_.to (mem-ext e z) (d z)

record ZFCAxioms {ℓ}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : KernelLike Sig Q)
                 : Set (lsuc (lsuc ℓ)) where
  field
    zf : ZFAxioms K

  open ZFAxioms zf public

  field
    AC : AC.AxiomOfChoice SetU _∈_ _≈_ pairing
