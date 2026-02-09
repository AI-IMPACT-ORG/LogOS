{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Reflection.QuanticNucleus where

open import LogOS.Prelude hiding (refl; trans) renaming (_⊔_ to _⊔ℓ_)
open import LogOS.Minimal.Prequantale public hiding (refl; trans)
open import LogOS.Minimal.Con using (ConPreorder; MonoOn; ≈CP⇒; ≈CP⇐)

record Nucleus {ℓ : Level} (Q : Prequantale {ℓ}) : Set (lsuc ℓ) where
  open Prequantale Q
    renaming (CP to CPQ; _⊔_ to _⊔Q_; _·_ to _·Q_; e to eQ)
    hiding (_≈_)
  field
    j         : Prequantale.Con Q → Prequantale.Con Q
    mono      : MonoOn CPQ j
    infl      : ∀ (c : Prequantale.Con Q) → ConPreorder._⊑_ CPQ c (j c)
    idemp-lax : ∀ (c : Prequantale.Con Q) → ConPreorder._⊑_ CPQ (j (j c)) (j c)
    join-pres
      : ∀ (a b : Prequantale.Con Q)
      → Prequantale._≈_ Q (j (a ⊔Q b)) (j a ⊔Q j b)
    mul-pres
      : ∀ (a b : Prequantale.Con Q)
      → Prequantale._≈_ Q (j (a ·Q b)) (j a ·Q j b)

open Nucleus public

record Fixed {ℓ : Level} {Q : Prequantale {ℓ}} (N : Nucleus Q) : Set ℓ where
  open Prequantale Q
  field
    val   : Prequantale.Con Q
    fixed : ConPreorder._⊑_ (Prequantale.CP Q) (j N val) val

open Fixed public

quotient
  : ∀ {ℓ} {Q : Prequantale {ℓ}} (N : Nucleus Q)
  → Prequantale.Con Q → Fixed N
quotient N c = record { val = j N c ; fixed = idemp-lax N c }

fixedConPreorder
  : ∀ {ℓ} {Q : Prequantale {ℓ}} (N : Nucleus Q)
  → ConPreorder ℓ
fixedConPreorder {Q = Q} N = record
  { Con  = Fixed N
  ; _⊑_  = λ x y → ConPreorder._⊑_ (Prequantale.CP Q) (val x) (val y)
  ; refl = ConPreorder.refl (Prequantale.CP Q)
  ; trans = ConPreorder.trans (Prequantale.CP Q)
  }

fixedPrequantale
  : ∀ {ℓ} {Q : Prequantale {ℓ}} (N : Nucleus Q)
  → Prequantale {ℓ}
fixedPrequantale {Q = Q} N =
  record
    { CP = fixedConPreorder N
    ; _⊔_ = λ x y → record
        { val = Prequantale._⊔_ Q (val x) (val y)
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
            in ConPreorder.trans (Prequantale.CP Q) step₁ step₂
        }
    ; ⊥ = quotient N (Prequantale.⊥ Q)
    ; ⊥-least = λ x →
        let
          step₁ = mono N (Prequantale.⊥-least Q (val x))
          step₂ = fixed x
        in ConPreorder.trans (Prequantale.CP Q) step₁ step₂
    ; ⊔-ub₁ = λ x y → Prequantale.⊔-ub₁ Q (val x) (val y)
    ; ⊔-ub₂ = λ x y → Prequantale.⊔-ub₂ Q (val x) (val y)
    ; ⊔-least = λ {x} {y} {z} x≤z y≤z → Prequantale.⊔-least Q x≤z y≤z
    ; _·_ = λ x y → record
        { val = Prequantale._·_ Q (val x) (val y)
        ; fixed =
            let
              step₁ = fst (mul-pres N (val x) (val y))
              step₂ = Prequantale.·-mono Q (fixed x) (fixed y)
            in ConPreorder.trans (Prequantale.CP Q) step₁ step₂
        }
    ; e = quotient N (Prequantale.e Q)
    ; ·-mono = λ {x} {y} {z} {w} x≤y z≤w → Prequantale.·-mono Q x≤y z≤w
    ; ·-assoc = λ x y z → Prequantale.·-assoc Q (val x) (val y) (val z)
    ; ·-idl = λ x →
        let
            open ConPreorder (Prequantale.CP Q)
            eQ = Prequantale.e Q
            step₁ : ConPreorder._⊑_ (Prequantale.CP Q) (Prequantale._·_ Q (j N eQ) (val x)) (val x)
            step₁ =
              trans
                (Prequantale.·-mono Q (ConPreorder.refl (Prequantale.CP Q)) (infl N (val x)))
                (trans
                  (snd (mul-pres N eQ (val x)))
                  (trans
                    (mono N (fst (Prequantale.·-idl Q (val x))))
                    (fixed x)))
            step₂ : ConPreorder._⊑_ (Prequantale.CP Q) (val x) (Prequantale._·_ Q (j N eQ) (val x))
            step₂ =
              trans
                (infl N (val x))
                (trans
                  (mono N (snd (Prequantale.·-idl Q (val x))))
                  (trans
                    (fst (mul-pres N eQ (val x)))
                    (Prequantale.·-mono Q (ConPreorder.refl (Prequantale.CP Q)) (fixed x))))
        in step₁ , step₂
    ; ·-idr = λ x →
        let
            open ConPreorder (Prequantale.CP Q)
            eQ = Prequantale.e Q
            step₁ : ConPreorder._⊑_ (Prequantale.CP Q) (Prequantale._·_ Q (val x) (j N eQ)) (val x)
            step₁ =
              trans
                (Prequantale.·-mono Q (infl N (val x)) (ConPreorder.refl (Prequantale.CP Q)))
                (trans
                  (snd (mul-pres N (val x) eQ))
                  (trans
                    (mono N (fst (Prequantale.·-idr Q (val x))))
                    (fixed x)))
            step₂ : ConPreorder._⊑_ (Prequantale.CP Q) (val x) (Prequantale._·_ Q (val x) (j N eQ))
            step₂ =
              trans
                (infl N (val x))
                (trans
                  (mono N (snd (Prequantale.·-idr Q (val x))))
                  (trans
                    (fst (mul-pres N (val x) eQ))
                    (Prequantale.·-mono Q (fixed x) (ConPreorder.refl (Prequantale.CP Q)))))
        in step₁ , step₂
    ; ·-distl-⊔ = λ x y z → Prequantale.·-distl-⊔ Q (val x) (val y) (val z)
    ; ·-distr-⊔ = λ x y z → Prequantale.·-distr-⊔ Q (val x) (val y) (val z)
    }

factorise
  : ∀ {ℓ ℓA} {Q : Prequantale {ℓ}} (N : Nucleus Q)
    {A : Set ℓA}
    (f : Prequantale.Con Q → A)
    (stable : ∀ x → f (j N x) ≡ f x)
  → Σ (Fixed N → A) (λ g → ∀ x → g (quotient N x) ≡ f x)
factorise N f stable =
  (λ x → f (val x)) , (λ x → stable x)

-- --------------------------------------------------------------------------
-- Nucleus-stable morphisms and quotient universal property

StableUnderNucleus
  : ∀ {ℓ₁ ℓ₂ : Level}
    {Q : Prequantale {ℓ₁}} (N : Nucleus Q)
    {R : Prequantale {ℓ₂}}
  → PrequantaleMor Q R → Set (ℓ₁ ⊔ℓ ℓ₂)
StableUnderNucleus N {R = R} f =
  ∀ x → Prequantale._≈_ R (map f (j N x)) (map f x)

quotientMor
  : ∀ {ℓ} {Q : Prequantale {ℓ}} (N : Nucleus Q)
  → PrequantaleMor Q (fixedPrequantale N)
quotientMor {Q = Q} N =
  record
    { map = quotient N
    ; mono = λ {a} {b} a≤b → mono N a≤b
    ; ⊥-pres = ≈-refl {Q = fixedPrequantale N} {a = quotient N (Prequantale.⊥ Q)}
    ; ⊔-pres = λ a b →
        -- Values are definitionally the same (`j (a ⊔ b)` on both sides).
        fst (join-pres N a b) , snd (join-pres N a b)
    ; e-pres = ≈-refl {Q = fixedPrequantale N} {a = quotient N (Prequantale.e Q)}
    ; ·-pres = λ a b →
        fst (mul-pres N a b) , snd (mul-pres N a b)
    }

factoriseMor
  : ∀ {ℓ₁ ℓ₂ : Level}
    {Q : Prequantale {ℓ₁}} (N : Nucleus Q)
    {R : Prequantale {ℓ₂}}
    (f : PrequantaleMor Q R)
    (stable : StableUnderNucleus N f)
  → Σ (PrequantaleMor (fixedPrequantale N) R)
      (λ g → ∀ x → Prequantale._≈_ R (map g (quotient N x)) (map f x))
factoriseMor {Q = Q} N {R = R} f stable =
  g , comm
  where
    module Rr = Prequantale R

    g : PrequantaleMor (fixedPrequantale N) R
    g =
      record
        { map = λ x → map f (val x)
        ; mono = λ {x} {y} x≤y → mono f x≤y
        ; ⊥-pres =
            -- ⊥ in `fixedPrequantale` is `quotient N ⊥` (val = j ⊥).
            let
              step₁ = stable (Prequantale.⊥ Q)
              step₂ = ⊥-pres f
            in ≈-trans {Q = R} step₁ step₂
        ; ⊔-pres = λ x y → ⊔-pres f (val x) (val y)
        ; e-pres =
            let
              step₁ = stable (Prequantale.e Q)
              step₂ = e-pres f
            in ≈-trans {Q = R} step₁ step₂
        ; ·-pres = λ x y → ·-pres f (val x) (val y)
        }

    comm : ∀ x → Prequantale._≈_ R (map g (quotient N x)) (map f x)
    comm x = stable x

factoriseMor-unique
  : ∀ {ℓ₁ ℓ₂ : Level}
    {Q : Prequantale {ℓ₁}} (N : Nucleus Q)
    {R : Prequantale {ℓ₂}}
    (f : PrequantaleMor Q R)
    (stable : StableUnderNucleus N f)
    (g : PrequantaleMor (fixedPrequantale N) R)
  → (∀ x → Prequantale._≈_ R (map g (quotient N x)) (map f x))
  → g ≈Mor proj₁ (factoriseMor N f stable)
factoriseMor-unique {Q = Q} N {R = R} f stable g g∘q≈f x =
  let
    module Rr = Prequantale R

    -- `x` is equivalent (in the fixed-point preorder) to `quotient (val x)`.
    x≤q : Prequantale._⊑_ (fixedPrequantale N) x (quotient N (val x))
    x≤q = infl N (val x)

    q≤x : Prequantale._⊑_ (fixedPrequantale N) (quotient N (val x)) x
    q≤x = fixed x

    gx≤ : Rr._⊑_ (map g x) (map g (quotient N (val x)))
    gx≤ = mono g x≤q

    gx≥ : Rr._⊑_ (map g (quotient N (val x))) (map g x)
    gx≥ = mono g q≤x

    -- Rewrite `g (quotient (val x))` to `f (val x)`.
    gq≈f : Prequantale._≈_ R (map g (quotient N (val x))) (map f (val x))
    gq≈f = g∘q≈f (val x)

  in
  (ConPreorder.trans (Rr.CP) gx≤ (≈CP⇒ {CP = Rr.CP} gq≈f))
  ,
  (ConPreorder.trans (Rr.CP) (≈CP⇐ {CP = Rr.CP} gq≈f) gx≥)
