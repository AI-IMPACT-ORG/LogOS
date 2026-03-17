{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Lift where

-- A minimal “partiality”/lifting construction on preorders:
-- add a fresh bottom element (undefined), keeping the same carrier level.
--
-- Implementation note:
-- we use `⊤ ⊎ Con CP` (Prelude sum) to stay stdlib-free.
-- - `inj₁ ttℓ` = undefined (bottom)
-- - `inj₂ x`   = defined value `x`

open import LogOS.Prelude
open import LogOS.LT.ConPreorder as CPR using (ConPreorder; Con; MonoMap; _⊑_; _≈_; refl⊑)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

LiftCon : ∀ {ℓCon ℓRel : Level} → ConPreorder ℓCon ℓRel → Set ℓCon
LiftCon {ℓCon} CP = ⊤ {ℓCon} ⊎ Con CP

none : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel} → LiftCon CP
none = inj₁ ttℓ

some : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel} → Con CP → LiftCon CP
some = inj₂

-- The lifted preorder (same universes as the base preorder).
LiftCP : ∀ {ℓCon ℓRel : Level} → ConPreorder ℓCon ℓRel → ConPreorder ℓCon ℓRel
LiftCP {ℓCon} {ℓRel} CP =
  record
    { Con   = LiftCon CP
    ; _⊑_   = λ a b → _⊑ᴸ_ a b
    ; refl  = λ {c} → reflᴸ {c = c}
    ; trans = λ {a} {b} {c} → transᴸ {a = a} {b = b} {c = c}
    }
  where
    infix 4 _⊑ᴸ_
    _⊑ᴸ_ : LiftCon CP → LiftCon CP → Set ℓRel
    _⊑ᴸ_ (inj₁ ttℓ) _ = ⊤ {ℓRel}
    _⊑ᴸ_ (inj₂ _) (inj₁ ttℓ) = ⊥ {ℓRel}
    _⊑ᴸ_ (inj₂ x) (inj₂ y) = CPR._⊑_ CP x y

    reflᴸ : ∀ {c : LiftCon CP} → _⊑ᴸ_ c c
    reflᴸ {c = inj₁ ttℓ} = tt {ℓ = ℓRel}
    reflᴸ {c = inj₂ c} = ConPreorder.refl CP

    transᴸ
      : ∀ {a b c : LiftCon CP} → _⊑ᴸ_ a b → _⊑ᴸ_ b c → _⊑ᴸ_ a c
    transᴸ {a = inj₁ ttℓ} _ _ = tt {ℓ = ℓRel}
    transᴸ {a = inj₂ _} {b = inj₁ ttℓ} () _
    transᴸ {a = inj₂ _} {b = inj₂ _} {c = inj₁ ttℓ} _ ()
    transᴸ {a = inj₂ x} {b = inj₂ y} {c = inj₂ z} xy yz =
      let
        module R = ≤-Reasoning CP
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        x ⊑⟨ xy ⟩
        y ⊑⟨ yz ⟩
        z ∎⊑

-- Transitivity for the lifted preorder (`LiftCP`) as a reusable lemma.
--
-- Note: using `ConPreorder.trans (LiftCP CP)` directly can require explicit
-- implicit-argument instantiation; this lemma avoids that friction and keeps
-- downstream proofs stable.
transLiftCP
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
    {a b c : LiftCon CP}
  → _⊑_ (LiftCP CP) a b
  → _⊑_ (LiftCP CP) b c
  → _⊑_ (LiftCP CP) a c
transLiftCP {ℓRel = ℓRel} {CP = CP} {a = inj₁ ttℓ} _ _ = tt {ℓ = ℓRel}
transLiftCP {CP = CP} {a = inj₂ _} {b = inj₁ ttℓ} () _
transLiftCP {CP = CP} {a = inj₂ _} {b = inj₂ _} {c = inj₁ ttℓ} _ ()
transLiftCP {CP = CP} {a = inj₂ x} {b = inj₂ y} {c = inj₂ z} xy yz =
  let
    module R = ≤-Reasoning CP
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    x ⊑⟨ xy ⟩
    y ⊑⟨ yz ⟩
    z ∎⊑

returnᴸ
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → Con CP → Con (LiftCP CP)
returnᴸ {CP = CP} x = some {CP = CP} x

bindᴸ
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
  → Con (LiftCP A)
  → (Con A → Con (LiftCP B))
  → Con (LiftCP B)
bindᴸ {B = B} (inj₁ ttℓ) _ = none {CP = B}
bindᴸ (inj₂ a) k = k a

-- --------------------------------------------------------------------------
-- Kleisli laws (definitional equalities).

bindᴸ-returnᴸ-left
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
    (a : Con A)
    (k : Con A → Con (LiftCP B))
  → bindᴸ {A = A} {B = B} (returnᴸ {CP = A} a) k ≡ k a
bindᴸ-returnᴸ-left _ _ = refl

bindᴸ-returnᴸ-left≈
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
    (a : Con A)
    (k : Con A → Con (LiftCP B))
  → _≈_ (LiftCP B)
      (bindᴸ {A = A} {B = B} (returnᴸ {CP = A} a) k)
      (k a)
bindᴸ-returnᴸ-left≈ {A = A} {B = B} a k =
  ( refl⊑ (LiftCP B) {c = k a}
  , refl⊑ (LiftCP B) {c = k a}
  )

bindᴸ-returnᴸ-right
  : ∀ {ℓCon ℓRel : Level}
    {A : ConPreorder ℓCon ℓRel}
    (m : Con (LiftCP A))
  → bindᴸ {A = A} {B = A} m (returnᴸ {CP = A}) ≡ m
bindᴸ-returnᴸ-right (inj₁ ttℓ) = refl
bindᴸ-returnᴸ-right (inj₂ _) = refl

bindᴸ-returnᴸ-right≈
  : ∀ {ℓCon ℓRel : Level}
    {A : ConPreorder ℓCon ℓRel}
    (m : Con (LiftCP A))
  → _≈_ (LiftCP A)
      (bindᴸ {A = A} {B = A} m (returnᴸ {CP = A}))
      m
bindᴸ-returnᴸ-right≈ {A = A} (inj₁ ttℓ) =
  ( refl⊑ (LiftCP A) {c = none {CP = A}}
  , refl⊑ (LiftCP A) {c = none {CP = A}}
  )
bindᴸ-returnᴸ-right≈ {A = A} (inj₂ a) =
  ( refl⊑ (LiftCP A) {c = inj₂ a}
  , refl⊑ (LiftCP A) {c = inj₂ a}
  )

bindᴸ-assoc
  : ∀ {ℓCon ℓRel : Level}
    {A B C : ConPreorder ℓCon ℓRel}
    (m : Con (LiftCP A))
    (k : Con A → Con (LiftCP B))
    (l : Con B → Con (LiftCP C))
  → bindᴸ {A = B} {B = C} (bindᴸ {A = A} {B = B} m k) l
    ≡
    bindᴸ {A = A} {B = C} m (λ a → bindᴸ {A = B} {B = C} (k a) l)
bindᴸ-assoc (inj₁ ttℓ) _ _ = refl
bindᴸ-assoc (inj₂ _) _ _ = refl

bindᴸ-assoc≈
  : ∀ {ℓCon ℓRel : Level}
    {A B C : ConPreorder ℓCon ℓRel}
    (m : Con (LiftCP A))
    (k : Con A → Con (LiftCP B))
    (l : Con B → Con (LiftCP C))
  → _≈_ (LiftCP C)
      (bindᴸ {A = B} {B = C} (bindᴸ {A = A} {B = B} m k) l)
      (bindᴸ {A = A} {B = C} m (λ a → bindᴸ {A = B} {B = C} (k a) l))
bindᴸ-assoc≈ {C = C} (inj₁ ttℓ) k l =
  ( refl⊑ (LiftCP C) {c = none {CP = C}}
  , refl⊑ (LiftCP C) {c = none {CP = C}}
  )
bindᴸ-assoc≈ {C = C} (inj₂ a) k l =
  ( refl⊑ (LiftCP C) {c = bindᴸ (k a) l}
  , refl⊑ (LiftCP C) {c = bindᴸ (k a) l}
  )

-- Monotonicity of bind (left argument) requires monotonicity of the continuation.
bindᴸ-mono-l
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
    {k : Con A → Con (LiftCP B)}
  → MonoMap A (LiftCP B) k
  → ∀ {x y}
  → CPR._⊑_ (LiftCP {ℓCon = ℓCon} {ℓRel = ℓRel} A) x y
  → CPR._⊑_ (LiftCP {ℓCon = ℓCon} {ℓRel = ℓRel} B)
      (bindᴸ {A = A} {B = B} x k)
      (bindᴸ {A = A} {B = B} y k)
bindᴸ-mono-l {ℓRel = ℓRel} monoK {x = inj₁ ttℓ} {y} _ = tt {ℓ = ℓRel}
bindᴸ-mono-l monoK {x = inj₂ _} {y = inj₁ ttℓ} ()
bindᴸ-mono-l monoK {x = inj₂ a} {y = inj₂ b} ab = monoK ab

-- Monotonicity of bind (right argument) is pointwise (no monotonicity of the continuation needed).
bindᴸ-mono-r
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
    {x : Con (LiftCP A)}
    {k k' : Con A → Con (LiftCP B)}
  → (∀ a → CPR._⊑_ (LiftCP {ℓCon = ℓCon} {ℓRel = ℓRel} B) (k a) (k' a))
  → CPR._⊑_ (LiftCP {ℓCon = ℓCon} {ℓRel = ℓRel} B)
      (bindᴸ {A = A} {B = B} x k)
      (bindᴸ {A = A} {B = B} x k')
bindᴸ-mono-r {ℓRel = ℓRel} {x = inj₁ ttℓ} _ = tt {ℓ = ℓRel}
bindᴸ-mono-r {x = inj₂ a} kk' = kk' a
