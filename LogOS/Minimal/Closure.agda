{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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
-- particular distinguished fixed-point witness.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder; MonoOn; MonoMap; PartialOrder; compMonoMap; idMonoMap; _≈CP_)
open import LogOS.Syntax.Prop using (¬_)

record ClosureOp {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    cl        : Con → Con
    mono      : MonoOn CP cl
    infl      : ∀ c → _⊑_ c (cl c)
    idemp-lax : ∀ c → _⊑_ (cl (cl c)) (cl c)

open ClosureOp public

-- ============================================================================
-- Textbook notation (η/μ)
-- ============================================================================
--
-- Interpretation (preorder-as-category): a closure operator behaves like an
-- idempotent monad:
-- - η  is inflation (unit):      c ⊑ J c
-- - μ  is lax idempotence:       J (J c) ⊑ J c
--
-- We keep these in a nested module to avoid polluting the global namespace
-- (other parts of LogOS use `μ` for Kleene-style μ (least pre-fixed points;
-- fixed points only under explicit continuity assumptions)).

module Notation where
  η
    : ∀ {ℓ}
      {CP : ConPreorder ℓ}
    → (J : ClosureOp CP)
    → (c : ConPreorder.Con CP)
    → ConPreorder._⊑_ CP c (cl J c)
  η J c = infl J c

  μ
    : ∀ {ℓ}
      {CP : ConPreorder ℓ}
    → (J : ClosureOp CP)
    → (c : ConPreorder.Con CP)
    → ConPreorder._⊑_ CP (cl J (cl J c)) (cl J c)
  μ J c = idemp-lax J c

-- Derived convenience: idempotence as mutual refinement.
--
-- `ClosureOp` stores only the lax direction `cl (cl c) ⊑ cl c`. The other
-- direction follows from monotonicity + inflation (`mono (infl c)`), but having
-- it as a lemma prevents later “math drift” where users forget that this is
-- available.

idemp
  : ∀ {ℓ}
    {CP : ConPreorder ℓ}
  → (C : ClosureOp CP)
  → (c : ConPreorder.Con CP)
  → _≈CP_ CP (cl C c) (cl C (cl C c))
idemp {CP = CP} C c =
  (mono C (infl C c) , idemp-lax C c)

-- Antisymmetry upgrade: in a partial order, idempotence holds as equality.

idemp≡
  : ∀ {ℓ}
    {CP : ConPreorder ℓ}
  → PartialOrder CP
  → (C : ClosureOp CP)
  → (c : ConPreorder.Con CP)
  → cl C (cl C c) ≡ cl C c
idemp≡ {CP = CP} po C c =
  PartialOrder.antisym po (idemp-lax C c) (mono C (infl C c))

-- Degeneracy guard: the closure is not the identity (it changes at least one element).
--
-- This is a lightweight “properness” witness for forcing-style uses of
-- `ClosureOp`: it rules out the completely trivial modality where everything is
-- already closed.

record NontrivialClosureOp {ℓ : Level} (CP : ConPreorder ℓ) (J : ClosureOp CP) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    witness : Con
    not-closed : ¬ (_⊑_ (cl J witness) witness)

-- Lax preservation of closure along a map.
--
-- No monotonicity of `map` is assumed here; it is usually provided by the
-- surrounding structure (e.g. a ConAlg hom). The two carrier preorders may
-- live in different universes.
record ClosureHom {ℓ₁ ℓ₂ : Level}
                  (CP₁ : ConPreorder ℓ₁)
                  (CP₂ : ConPreorder ℓ₂)
                  (C₁ : ClosureOp CP₁)
                  (C₂ : ClosureOp CP₂)
                  (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                  : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  open ConPreorder CP₂ using (_⊑_)
  open ClosureOp C₁ renaming (cl to cl₁)
  open ClosureOp C₂ renaming (cl to cl₂)
  field
    preserves-cl : ∀ c → _⊑_ (map (cl₁ c)) (cl₂ (map c))

open ClosureHom public

-- Convenience bundle: a closure homomorphism together with monotonicity of the
-- underlying map.

record ClosureHomMono {ℓ₁ ℓ₂ : Level}
                      (CP₁ : ConPreorder ℓ₁)
                      (CP₂ : ConPreorder ℓ₂)
                      (C₁ : ClosureOp CP₁)
                      (C₂ : ClosureOp CP₂)
                      (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    core     : ClosureHom CP₁ CP₂ C₁ C₂ map
    mono-map : MonoMap CP₁ CP₂ map

  open ClosureHom core public

mkClosureHomMono
  : ∀ {ℓ₁ ℓ₂ : Level}
    {CP₁ : ConPreorder ℓ₁} {CP₂ : ConPreorder ℓ₂}
    {C₁ : ClosureOp CP₁} {C₂ : ClosureOp CP₂}
    {map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
  → MonoMap CP₁ CP₂ map
  → ClosureHom CP₁ CP₂ C₁ C₂ map
  → ClosureHomMono CP₁ CP₂ C₁ C₂ map
mkClosureHomMono mono core = record { core = core ; mono-map = mono }

-- Small combinators ----------------------------------------------------------

idClosureHom
  : ∀ {ℓ}
    {CP : ConPreorder ℓ}
    (C : ClosureOp CP)
  → ClosureHom CP CP C C (λ x → x)
idClosureHom {CP = CP} C =
  record { preserves-cl = λ _ → ConPreorder.refl CP }

idClosureHomMono
  : ∀ {ℓ}
    {CP : ConPreorder ℓ}
    (C : ClosureOp CP)
  → ClosureHomMono CP CP C C (λ x → x)
idClosureHomMono {CP = CP} C =
  mkClosureHomMono (idMonoMap {CP = CP}) (idClosureHom {CP = CP} C)

composeClosureHom
  : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
    {CP₁ : ConPreorder ℓ₁}
    {CP₂ : ConPreorder ℓ₂}
    {CP₃ : ConPreorder ℓ₃}
    {C₁ : ClosureOp CP₁}
    {C₂ : ClosureOp CP₂}
    {C₃ : ClosureOp CP₃}
    {f : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
    {g : ConPreorder.Con CP₂ → ConPreorder.Con CP₃}
  → MonoMap CP₂ CP₃ g
  → ClosureHom CP₁ CP₂ C₁ C₂ f
  → ClosureHom CP₂ CP₃ C₂ C₃ g
  → ClosureHom CP₁ CP₃ C₁ C₃ (λ x → g (f x))
composeClosureHom {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = f} {g = g} monoG hf hg =
  record
    { preserves-cl = λ c →
        ConPreorder.trans CP₃
          (monoG (preserves-cl hf c))
          (preserves-cl hg (f c))
    }

composeClosureHomMono
  : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
    {CP₁ : ConPreorder ℓ₁}
    {CP₂ : ConPreorder ℓ₂}
    {CP₃ : ConPreorder ℓ₃}
    {C₁ : ClosureOp CP₁}
    {C₂ : ClosureOp CP₂}
    {C₃ : ClosureOp CP₃}
    {f : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
    {g : ConPreorder.Con CP₂ → ConPreorder.Con CP₃}
  → ClosureHomMono CP₁ CP₂ C₁ C₂ f
  → ClosureHomMono CP₂ CP₃ C₂ C₃ g
  → ClosureHomMono CP₁ CP₃ C₁ C₃ (λ x → g (f x))
composeClosureHomMono {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = f} {g = g} hf hg =
  record
    { core =
        composeClosureHom
          (ClosureHomMono.mono-map hg)
          (ClosureHomMono.core hf)
          (ClosureHomMono.core hg)
    ; mono-map =
        compMonoMap {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = f} {g = g}
          (ClosureHomMono.mono-map hf)
          (ClosureHomMono.mono-map hg)
    }
