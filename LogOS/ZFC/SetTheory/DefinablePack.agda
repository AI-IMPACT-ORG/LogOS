{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.DefinablePack where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel
open import LogOS.API.Kernel.Eq using (module ForKernel)
open import LogOS.Syntax.Prop using (_↔_; ¬_; intro)
open import LogOS.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)

-- 80/20 pack: ZFC where the “schemata” are restricted to DSL-definable data.
--
-- This avoids quantifying over arbitrary Agda predicates `SetU → Set`,
-- which is exactly what causes ballooning obligations (and is not generally
-- constructively realizable without extra structure).
--
-- Remark (Metamath-style): this “definable schemata” approach is exactly the
-- usual trick for getting a practical proof assistant without impredicative
-- meta-level quantification. Instead of Separation/Replacement ranging over
-- all Agda predicates/functions, they range over *codes* (formulas/graphs) in
-- an object language. Metamath enforces this by construction (everything is a
-- string in the object language); LogOS packages it as an explicit interface.
--
-- If you want textbook schemata (Separation/Replacement over all Agda
-- predicates/functions), use `LogOS.ZFC.SetTheory.FullUpgradeFromDefinable`
-- to make the needed “representability by codes” assumptions explicit.
-- In this repository, the corresponding module is `LogOS/ZFC/SetTheory/FullUpgradeFromDefinable.agda`.
--
-- We keep the same core surface as `LogOS.ZFC.SetTheory.Pack.ZFAxioms`,
-- but replace Separation/Replacement with *coded* versions.

record ZFAxiomsᵈ {ℓ}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q)
                 : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  open ForKernel K
  field
    SetU   : Set ℓ
    _∈_    : SetU → SetU → Set ℓ

  -- Membership-induced observational preorder/equality.
  infix 4 _∈_ _⊑_ _≈_
  _⊑_ : SetU → SetU → Set ℓ
  x ⊑ y = ∀ z → (z ∈ x) → (z ∈ y)

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

  extensionality : ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≈ y
  extensionality x y hyp =
    ( (λ z exz → _↔_.to (hyp z) exz)
    , (λ z eyz → _↔_.from (hyp z) eyz)
    )

  mem-ext : ∀ {x y} → x ≈ y → ∀ z → (z ∈ x) ↔ (z ∈ y)
  mem-ext {x} {y} (xy , yx) z = intro (xy z) (yx z)

  field
    -- Code interpretation into the set universe (typically via the kernel’s decode view).
    ⟦_⟧     : Code → SetU
    by-decode≈ : ∀ {γ δ} → γ ≃K δ → ⟦ γ ⟧ ≈ ⟦ δ ⟧
    mem-congL : ∀ {x y} → x ≈ y → ∀ z → (x ∈ z) ↔ (y ∈ z)

    empty : Σ SetU (λ e → ∀ z → ¬ (z ∈ e))
    pairing : ∀ x y → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ ((z ≈ x) ⊎ (z ≈ y)))
    union  : ∀ x → Σ SetU (λ u → ∀ z → (z ∈ u) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y))))
    powerset : ∀ x → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ (∀ w → w ∈ z → w ∈ x))

    zeroS : SetU
    zeroS-empty : ∀ z → ¬ (z ∈ zeroS)
    succ  : SetU → SetU
    mem-succ↔ : ∀ x z → (z ∈ succ x) ↔ ((z ∈ x) ⊎ (z ≈ x))
    infinity : Σ SetU (λ ω → (∀ z → (z ∈ ω) ↔ ((z ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ ω × (z ≈ succ y))))))

    -- Definable schemata: a “predicate” is a Code whose extension is membership in ⟦γ⟧.
    --
    -- This corresponds to *bounded* (parameterised) separation at the surface level:
    -- “collect the elements of x that also lie in ⟦γ⟧”.
    separationᵈ
      : (γ : Code) → ∀ x →
        Σ SetU (λ y → ∀ z → (z ∈ y) ↔ ((z ∈ x) × (z ∈ ⟦ γ ⟧)))

    -- Definable replacement: a “function” is given as a Code standing for its graph.
    --
    -- The intended reading is: `z ∈ y` iff ∃u∈x. Graph γ relates u to z.
    -- We keep the graph relation abstract as `Graph γ u z`.
    --
    -- Replacement is stated in the standard way: it applies when the graph is
    -- *functional* (single-valued, up to `≈`).
    Graph : Code → SetU → SetU → Set ℓ

  -- “Functional” means: the graph is single-valued (up to `≈`).
  FunctionalGraph : (Graph : SetU → SetU → Set ℓ) → Set ℓ
  FunctionalGraph Graph = ∀ u z₁ z₂ → Graph u z₁ → Graph u z₂ → z₁ ≈ z₂

  field
    replacementᵈ
      : (γ : Code) → FunctionalGraph (Graph γ) → ∀ x →
        Σ SetU (λ y → ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → (u ∈ x) × Graph γ u z)))

    foundation : ∀ x → (x ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y))))

record ZFCAxiomsᵈ {ℓ}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q)
                 : Set (lsuc (lsuc ℓ)) where
  field
    zf : ZFAxiomsᵈ K

  open ZFAxiomsᵈ zf public

  field
    AC : AC.AxiomOfChoice SetU _∈_ _≈_ pairing
