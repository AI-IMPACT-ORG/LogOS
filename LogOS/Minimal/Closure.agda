{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Closure where

-- A tiny “closure operator / nucleus” interface on a constraint preorder.
--
-- This is intentionally independent of any fixed-point witness (`Th*`): many
-- applications (e.g. nuclei for forcing, publicisation/feasibility modalities,
-- auditability closures) want a closure operator but do not want to commit to a
-- particular distinguished fixed point.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPoset; MonoOn; MonoMap)

record ClosureOp {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    cl        : Con → Con
    mono      : MonoOn CP cl
    infl      : ∀ c → _⊑_ c (cl c)
    idemp-lax : ∀ c → _⊑_ (cl (cl c)) (cl c)

open ClosureOp public

-- Lax preservation of closure along a map.
--
-- No monotonicity of `map` is assumed here; it is usually provided by the
-- surrounding structure (e.g. a ConAlg hom). The two carrier preorders may
-- live in different universes.
record ClosureHom {ℓ₁ ℓ₂ : Level}
                  (CP₁ : ConPoset ℓ₁)
                  (CP₂ : ConPoset ℓ₂)
                  (C₁ : ClosureOp CP₁)
                  (C₂ : ClosureOp CP₂)
                  (map : ConPoset.Con CP₁ → ConPoset.Con CP₂)
                  : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  open ConPoset CP₂ using (_⊑_)
  open ClosureOp C₁ renaming (cl to cl₁)
  open ClosureOp C₂ renaming (cl to cl₂)
  field
    preserves-cl : ∀ c → _⊑_ (map (cl₁ c)) (cl₂ (map c))

open ClosureHom public

-- Small combinators ----------------------------------------------------------

idClosureHom
  : ∀ {ℓ}
    {CP : ConPoset ℓ}
    (C : ClosureOp CP)
  → ClosureHom CP CP C C (λ x → x)
idClosureHom {CP = CP} C =
  record { preserves-cl = λ _ → ConPoset.refl CP }

composeClosureHom
  : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
    {CP₁ : ConPoset ℓ₁}
    {CP₂ : ConPoset ℓ₂}
    {CP₃ : ConPoset ℓ₃}
    {C₁ : ClosureOp CP₁}
    {C₂ : ClosureOp CP₂}
    {C₃ : ClosureOp CP₃}
    {f : ConPoset.Con CP₁ → ConPoset.Con CP₂}
    {g : ConPoset.Con CP₂ → ConPoset.Con CP₃}
  → MonoMap CP₂ CP₃ g
  → ClosureHom CP₁ CP₂ C₁ C₂ f
  → ClosureHom CP₂ CP₃ C₂ C₃ g
  → ClosureHom CP₁ CP₃ C₁ C₃ (λ x → g (f x))
composeClosureHom {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = f} {g = g} monoG hf hg =
  record
    { preserves-cl = λ c →
        ConPoset.trans CP₃
          (monoG (preserves-cl hf c))
          (preserves-cl hg (f c))
    }
