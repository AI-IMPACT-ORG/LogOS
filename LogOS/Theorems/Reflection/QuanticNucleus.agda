{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Reflection.QuanticNucleus where

open import LogOS.Prelude hiding (refl; trans) renaming (_⊔_ to _⊔ℓ_)
open import LogOS.Algebra.Quantale public
open import LogOS.Minimal.Con using (ConPoset; MonoOn)

record Nucleus {ℓ : Level} (Q : Quantale {ℓ}) : Set (lsuc ℓ) where
  open Quantale Q
    renaming (CP to CPQ; _⊔_ to _⊔Q_; _·_ to _·Q_; e to eQ)
    hiding (_≈_)
  field
    j         : Quantale.Con Q → Quantale.Con Q
    mono      : MonoOn CPQ j
    infl      : ∀ (c : Quantale.Con Q) → ConPoset._⊑_ CPQ c (j c)
    idemp-lax : ∀ (c : Quantale.Con Q) → ConPoset._⊑_ CPQ (j (j c)) (j c)
    join-pres
      : ∀ (a b : Quantale.Con Q)
      → Quantale._≈_ Q (j (a ⊔Q b)) (j a ⊔Q j b)
    mul-pres
      : ∀ (a b : Quantale.Con Q)
      → Quantale._≈_ Q (j (a ·Q b)) (j a ·Q j b)

open Nucleus public

record Fixed {ℓ : Level} {Q : Quantale {ℓ}} (N : Nucleus Q) : Set ℓ where
  open Quantale Q
  field
    val   : Quantale.Con Q
    fixed : ConPoset._⊑_ (Quantale.CP Q) (j N val) val

open Fixed public

quotient
  : ∀ {ℓ} {Q : Quantale {ℓ}} (N : Nucleus Q)
  → Quantale.Con Q → Fixed N
quotient N c = record { val = j N c ; fixed = idemp-lax N c }

fixedConPoset
  : ∀ {ℓ} {Q : Quantale {ℓ}} (N : Nucleus Q)
  → ConPoset ℓ
fixedConPoset {Q = Q} N = record
  { Con  = Fixed N
  ; _⊑_  = λ x y → ConPoset._⊑_ (Quantale.CP Q) (val x) (val y)
  ; refl = ConPoset.refl (Quantale.CP Q)
  ; trans = ConPoset.trans (Quantale.CP Q)
  }

fixedQuantale
  : ∀ {ℓ} {Q : Quantale {ℓ}} (N : Nucleus Q)
  → Quantale {ℓ}
fixedQuantale {Q = Q} N =
  record
    { CP = fixedConPoset N
    ; _⊔_ = λ x y → record
        { val = Quantale._⊔_ Q (val x) (val y)
        ; fixed =
            let
              step₁ = fst (join-pres N (val x) (val y))
              step₂ =
                ⊔-mono
                  {Q = Q}
                  {a = j N (val x)}
                  {b = j N (val y)}
                  {c = val x}
                  {d = val y}
                  (fixed x)
                  (fixed y)
            in ConPoset.trans (Quantale.CP Q) step₁ step₂
        }
    ; ⊥ = quotient N (Quantale.⊥ Q)
    ; ⊥-least = λ x →
        let
          step₁ = mono N (Quantale.⊥-least Q (val x))
          step₂ = fixed x
        in ConPoset.trans (Quantale.CP Q) step₁ step₂
    ; ⊔-ub₁ = λ x y → Quantale.⊔-ub₁ Q (val x) (val y)
    ; ⊔-ub₂ = λ x y → Quantale.⊔-ub₂ Q (val x) (val y)
    ; ⊔-least = λ {x} {y} {z} x≤z y≤z → Quantale.⊔-least Q x≤z y≤z
    ; _·_ = λ x y → record
        { val = Quantale._·_ Q (val x) (val y)
        ; fixed =
            let
              step₁ = fst (mul-pres N (val x) (val y))
              step₂ = Quantale.·-mono Q (fixed x) (fixed y)
            in ConPoset.trans (Quantale.CP Q) step₁ step₂
        }
    ; e = quotient N (Quantale.e Q)
    ; ·-mono = λ {x} {y} {z} {w} x≤y z≤w → Quantale.·-mono Q x≤y z≤w
    ; ·-assoc = λ x y z → Quantale.·-assoc Q (val x) (val y) (val z)
    ; ·-idl = λ x →
        let
            open ConPoset (Quantale.CP Q)
            eQ = Quantale.e Q
            step₁ : ConPoset._⊑_ (Quantale.CP Q) (Quantale._·_ Q (j N eQ) (val x)) (val x)
            step₁ =
              trans
                (Quantale.·-mono Q refl (infl N (val x)))
                (trans
                  (snd (mul-pres N eQ (val x)))
                  (trans
                    (mono N (fst (Quantale.·-idl Q (val x))))
                    (fixed x)))
            step₂ : ConPoset._⊑_ (Quantale.CP Q) (val x) (Quantale._·_ Q (j N eQ) (val x))
            step₂ =
              trans
                (infl N (val x))
                (trans
                  (mono N (snd (Quantale.·-idl Q (val x))))
                  (trans
                    (fst (mul-pres N eQ (val x)))
                    (Quantale.·-mono Q refl (fixed x))))
        in step₁ , step₂
    ; ·-idr = λ x →
        let
            open ConPoset (Quantale.CP Q)
            eQ = Quantale.e Q
            step₁ : ConPoset._⊑_ (Quantale.CP Q) (Quantale._·_ Q (val x) (j N eQ)) (val x)
            step₁ =
              trans
                (Quantale.·-mono Q (infl N (val x)) refl)
                (trans
                  (snd (mul-pres N (val x) eQ))
                  (trans
                    (mono N (fst (Quantale.·-idr Q (val x))))
                    (fixed x)))
            step₂ : ConPoset._⊑_ (Quantale.CP Q) (val x) (Quantale._·_ Q (val x) (j N eQ))
            step₂ =
              trans
                (infl N (val x))
                (trans
                  (mono N (snd (Quantale.·-idr Q (val x))))
                  (trans
                    (fst (mul-pres N (val x) eQ))
                    (Quantale.·-mono Q (fixed x) refl)))
        in step₁ , step₂
    ; ·-distl-⊔ = λ x y z → Quantale.·-distl-⊔ Q (val x) (val y) (val z)
    ; ·-distr-⊔ = λ x y z → Quantale.·-distr-⊔ Q (val x) (val y) (val z)
    }

factorise
  : ∀ {ℓ ℓA} {Q : Quantale {ℓ}} (N : Nucleus Q)
    {A : Set ℓA}
    (f : Quantale.Con Q → A)
    (stable : ∀ x → f (j N x) ≡ f x)
  → Σ (Fixed N → A) (λ g → ∀ x → g (quotient N x) ≡ f x)
factorise N f stable =
  (λ x → f (val x)) , (λ x → stable x)

-- --------------------------------------------------------------------------
-- Nucleus-stable morphisms and quotient universal property

StableUnderNucleus
  : ∀ {ℓ₁ ℓ₂ : Level}
    {Q : Quantale {ℓ₁}} (N : Nucleus Q)
    {R : Quantale {ℓ₂}}
  → QuantaleMor Q R → Set (ℓ₁ ⊔ℓ ℓ₂)
StableUnderNucleus N {R = R} f =
  ∀ x → Quantale._≈_ R (map f (j N x)) (map f x)

quotientMor
  : ∀ {ℓ} {Q : Quantale {ℓ}} (N : Nucleus Q)
  → QuantaleMor Q (fixedQuantale N)
quotientMor {Q = Q} N =
  record
    { map = quotient N
    ; mono = λ {a} {b} a≤b → mono N a≤b
    ; ⊥-pres = ≈-refl {Q = fixedQuantale N} {a = quotient N (Quantale.⊥ Q)}
    ; ⊔-pres = λ a b →
        -- Values are definitionally the same (`j (a ⊔ b)` on both sides).
        fst (join-pres N a b) , snd (join-pres N a b)
    ; e-pres = ≈-refl {Q = fixedQuantale N} {a = quotient N (Quantale.e Q)}
    ; ·-pres = λ a b →
        fst (mul-pres N a b) , snd (mul-pres N a b)
    }

factoriseMor
  : ∀ {ℓ₁ ℓ₂ : Level}
    {Q : Quantale {ℓ₁}} (N : Nucleus Q)
    {R : Quantale {ℓ₂}}
    (f : QuantaleMor Q R)
    (stable : StableUnderNucleus N f)
  → Σ (QuantaleMor (fixedQuantale N) R)
      (λ g → ∀ x → Quantale._≈_ R (map g (quotient N x)) (map f x))
factoriseMor {Q = Q} N {R = R} f stable =
  g , comm
  where
    module Qr = Quantale R

    g : QuantaleMor (fixedQuantale N) R
    g =
      record
        { map = λ x → map f (val x)
        ; mono = λ {x} {y} x≤y → mono f x≤y
        ; ⊥-pres =
            -- ⊥ in `fixedQuantale` is `quotient N ⊥` (val = j ⊥).
            let
              step₁ = stable (Quantale.⊥ Q)
              step₂ = ⊥-pres f
            in ≈-trans {Q = R} step₁ step₂
        ; ⊔-pres = λ x y → ⊔-pres f (val x) (val y)
        ; e-pres =
            let
              step₁ = stable (Quantale.e Q)
              step₂ = e-pres f
            in ≈-trans {Q = R} step₁ step₂
        ; ·-pres = λ x y → ·-pres f (val x) (val y)
        }

    comm : ∀ x → Quantale._≈_ R (map g (quotient N x)) (map f x)
    comm x = stable x

factoriseMor-unique
  : ∀ {ℓ₁ ℓ₂ : Level}
    {Q : Quantale {ℓ₁}} (N : Nucleus Q)
    {R : Quantale {ℓ₂}}
    (f : QuantaleMor Q R)
    (stable : StableUnderNucleus N f)
    (g : QuantaleMor (fixedQuantale N) R)
  → (∀ x → Quantale._≈_ R (map g (quotient N x)) (map f x))
  → g ≈Mor proj₁ (factoriseMor N f stable)
factoriseMor-unique {Q = Q} N {R = R} f stable g g∘q≈f x =
  let
    module Qr = Quantale R

    -- `x` is equivalent (in the fixed-point preorder) to `quotient (val x)`.
    x≤q : Quantale._⊑_ (fixedQuantale N) x (quotient N (val x))
    x≤q = infl N (val x)

    q≤x : Quantale._⊑_ (fixedQuantale N) (quotient N (val x)) x
    q≤x = fixed x

    gx≤ : Qr._⊑_ (map g x) (map g (quotient N (val x)))
    gx≤ = mono g x≤q

    gx≥ : Qr._⊑_ (map g (quotient N (val x))) (map g x)
    gx≥ = mono g q≤x

    -- Rewrite `g (quotient (val x))` to `f (val x)`.
    gq≈f : Quantale._≈_ R (map g (quotient N (val x))) (map f (val x))
    gq≈f = g∘q≈f (val x)

  in
  (ConPoset.trans (Qr.CP) gx≤ (fst gq≈f))
  ,
  (ConPoset.trans (Qr.CP) (snd gq≈f) gx≥)
