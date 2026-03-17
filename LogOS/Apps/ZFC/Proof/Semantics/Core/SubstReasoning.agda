{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Core.SubstReasoning where

open import LogOS.Prelude using
  ( Level
  ; _≡_
  ; _×_
  ; _⊎_
  ; Σ
  ; _,_
  ; fst
  ; snd
  ; refl
  ; cong
  ; cong₂
  ; sym
  ; ℕ
  ; zero
  ; suc
  ; inj₁
  ; inj₂
  )

open import LogOS.Syntax.Prop using (_↔_; intro; to; from)
open import LogOS.LT.View using (μ)

open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Term; Formula
  ; Renaming
  ; liftRen
  ; renameTerm
  ; renameFormula
  ; liftTerm
  ; liftFormula
  ; substTermAt
  ; substFormulaAt
  ; cmpNat
  ; predNat
  ; less
  ; equal
  ; greater
  ; insert1Ren
  ; insert2Ren
  ; var; emptyT; pairT; unionT; powerT; succT; omegaT
  ; ⊥F; _∈F_; _≈F_; _⇒_; _∧F_; _∨F_; _↔F_; ∀F; ∃F
  )

open import LogOS.Apps.ZFC.Proof.Semantics.Core.ModelDef using (Model)

module ForModel {ℓ : Level} (M : Model {ℓ}) where
  open Model M
  open FO.D using (SuccV)

  ↔-trans : ∀ {A B C : Set ℓ} → A ↔ B → B ↔ C → A ↔ C
  ↔-trans ab bc = intro (λ a → to bc (to ab a)) (λ c → from ab (from bc c))

  renameVal : Renaming → Valuation → Valuation
  renameVal ρ ν n = ν (ρ n)

  ValEq : Valuation → Valuation → Set ℓ
  ValEq ρ σ = ∀ n → ρ n ≡ σ n

  valEqByCases01
    : ∀ {ρ σ}
    → ρ zero ≡ σ zero
    → ρ (suc zero) ≡ σ (suc zero)
    → (∀ n → ρ (suc (suc n)) ≡ σ (suc (suc n)))
    → ValEq ρ σ
  valEqByCases01 eq0 eq1 eq2 = λ where
    zero → eq0
    (suc zero) → eq1
    (suc (suc n)) → eq2 n

  extend-cong : ∀ {ρ σ} → ValEq ρ σ → ∀ x → ValEq (extend x ρ) (extend x σ)
  extend-cong eq x zero = refl
  extend-cong eq x (suc n) = eq n

  renameVal-liftRen-extend
    : ∀ (ρv : Renaming) (ν : Valuation) (x : SetU)
    → ValEq
        (renameVal (liftRen ρv) (extend x ν))
        (extend x (renameVal ρv ν))
  renameVal-liftRen-extend ρv ν x zero = refl
  renameVal-liftRen-extend ρv ν x (suc n) = refl

  insert1-separation-cong
    : ∀ (ρ : Valuation) (x y z : SetU)
    → ValEq
        (renameVal insert1Ren (extend z (extend y (extend x ρ))))
        (extend z (extend x ρ))
  insert1-separation-cong ρ x y z zero = refl
  insert1-separation-cong ρ x y z (suc zero) = refl
  insert1-separation-cong ρ x y z (suc (suc n)) = refl

  insert2-replacement-cong
    : ∀ (ρ : Valuation) (x y z u : SetU)
    → ValEq
        (renameVal insert2Ren (extend u (extend z (extend y (extend x ρ)))))
        (extend u (extend x ρ))
  insert2-replacement-cong ρ x y z u zero = refl
  insert2-replacement-cong ρ x y z u (suc zero) = refl
  insert2-replacement-cong ρ x y z u (suc (suc n)) = refl

  evalTerm-cong : ∀ {ρ σ} → ValEq ρ σ → (t : Term) → evalTerm t ρ ≡ evalTerm t σ
  evalTerm-cong eq (var n) = eq n
  evalTerm-cong eq emptyT = refl
  evalTerm-cong eq (pairT t u) =
    cong₂ pairSet (evalTerm-cong eq t) (evalTerm-cong eq u)
  evalTerm-cong eq (unionT t) = cong unionSet (evalTerm-cong eq t)
  evalTerm-cong eq (powerT t) = cong powersetSet (evalTerm-cong eq t)
  evalTerm-cong eq (succT t) = cong (μ SuccV) (evalTerm-cong eq t)
  evalTerm-cong eq omegaT = refl

  evalFormula-cong : ∀ {ρ σ} → ValEq ρ σ → (φ : Formula) → evalFormula φ ρ ↔ evalFormula φ σ
  evalFormula-cong eq ⊥F = intro (λ x → x) (λ x → x)
  evalFormula-cong eq (t ∈F u)
    rewrite evalTerm-cong eq t | evalTerm-cong eq u -- rewrite-justified:evalTerm-cong
    = intro (λ p → p) (λ p → p)
  evalFormula-cong eq (t ≈F u)
    rewrite evalTerm-cong eq t | evalTerm-cong eq u -- rewrite-justified:evalTerm-cong
    = intro (λ p → p) (λ p → p)
  evalFormula-cong eq (φ ⇒ ψ) =
    intro
      (λ f x → to (evalFormula-cong eq ψ) (f (from (evalFormula-cong eq φ) x)))
      (λ f x → from (evalFormula-cong eq ψ) (f (to (evalFormula-cong eq φ) x)))
  evalFormula-cong eq (φ ∧F ψ) =
    intro
      (λ where (p , q) → to (evalFormula-cong eq φ) p , to (evalFormula-cong eq ψ) q)
      (λ where (p , q) → from (evalFormula-cong eq φ) p , from (evalFormula-cong eq ψ) q)
  evalFormula-cong eq (φ ∨F ψ) =
    intro
      (λ where
        (inj₁ p) → inj₁ (to (evalFormula-cong eq φ) p)
        (inj₂ q) → inj₂ (to (evalFormula-cong eq ψ) q))
      (λ where
        (inj₁ p) → inj₁ (from (evalFormula-cong eq φ) p)
        (inj₂ q) → inj₂ (from (evalFormula-cong eq ψ) q))
  evalFormula-cong eq (φ ↔F ψ) =
    intro
      (λ p →
        intro
          (λ x → to (evalFormula-cong eq ψ) (to p (from (evalFormula-cong eq φ) x)))
          (λ y → to (evalFormula-cong eq φ) (from p (from (evalFormula-cong eq ψ) y))))
      (λ p →
        intro
          (λ x → from (evalFormula-cong eq ψ) (to p (to (evalFormula-cong eq φ) x)))
          (λ y → from (evalFormula-cong eq φ) (from p (to (evalFormula-cong eq ψ) y))))
  evalFormula-cong eq (∀F φ) =
    intro
      (λ f x → to (evalFormula-cong (extend-cong eq x) φ) (f x))
      (λ f x → from (evalFormula-cong (extend-cong eq x) φ) (f x))
  evalFormula-cong eq (∃F φ) =
    intro
      (λ where (x , px) → x , to (evalFormula-cong (extend-cong eq x) φ) px)
      (λ where (x , px) → x , from (evalFormula-cong (extend-cong eq x) φ) px)

  evalTerm-rename
    : ∀ (ρv : Renaming) (t : Term) (ν : Valuation)
    → evalTerm (renameTerm ρv t) ν ≡ evalTerm t (renameVal ρv ν)
  evalTerm-rename ρv (var n) ν = refl
  evalTerm-rename ρv emptyT ν = refl
  evalTerm-rename ρv (pairT t u) ν =
    cong₂ pairSet (evalTerm-rename ρv t ν) (evalTerm-rename ρv u ν)
  evalTerm-rename ρv (unionT t) ν = cong unionSet (evalTerm-rename ρv t ν)
  evalTerm-rename ρv (powerT t) ν = cong powersetSet (evalTerm-rename ρv t ν)
  evalTerm-rename ρv (succT t) ν = cong (μ SuccV) (evalTerm-rename ρv t ν)
  evalTerm-rename ρv omegaT ν = refl

  evalFormula-rename
    : ∀ (ρv : Renaming) (φ : Formula) (ν : Valuation)
    → evalFormula (renameFormula ρv φ) ν ↔ evalFormula φ (renameVal ρv ν)
  evalFormula-rename ρv ⊥F ν = intro (λ x → x) (λ x → x)
  evalFormula-rename ρv (t ∈F u) ν
    rewrite evalTerm-rename ρv t ν | evalTerm-rename ρv u ν -- rewrite-justified:evalTerm-rename
    = intro (λ p → p) (λ p → p)
  evalFormula-rename ρv (t ≈F u) ν
    rewrite evalTerm-rename ρv t ν | evalTerm-rename ρv u ν -- rewrite-justified:evalTerm-rename
    = intro (λ p → p) (λ p → p)
  evalFormula-rename ρv (φ ⇒ ψ) ν =
    intro
      (λ f x → to (evalFormula-rename ρv ψ ν) (f (from (evalFormula-rename ρv φ ν) x)))
      (λ f x → from (evalFormula-rename ρv ψ ν) (f (to (evalFormula-rename ρv φ ν) x)))
  evalFormula-rename ρv (φ ∧F ψ) ν =
    intro
      (λ where (p , q) → to (evalFormula-rename ρv φ ν) p , to (evalFormula-rename ρv ψ ν) q)
      (λ where (p , q) → from (evalFormula-rename ρv φ ν) p , from (evalFormula-rename ρv ψ ν) q)
  evalFormula-rename ρv (φ ∨F ψ) ν =
    intro
      (λ where
        (inj₁ p) → inj₁ (to (evalFormula-rename ρv φ ν) p)
        (inj₂ q) → inj₂ (to (evalFormula-rename ρv ψ ν) q))
      (λ where
        (inj₁ p) → inj₁ (from (evalFormula-rename ρv φ ν) p)
        (inj₂ q) → inj₂ (from (evalFormula-rename ρv ψ ν) q))
  evalFormula-rename ρv (φ ↔F ψ) ν =
    intro
      (λ p →
        intro
          (λ x → to (evalFormula-rename ρv ψ ν) (to p (from (evalFormula-rename ρv φ ν) x)))
          (λ y → to (evalFormula-rename ρv φ ν) (from p (from (evalFormula-rename ρv ψ ν) y))))
      (λ p →
        intro
          (λ x → from (evalFormula-rename ρv ψ ν) (to p (to (evalFormula-rename ρv φ ν) x)))
          (λ y → from (evalFormula-rename ρv φ ν) (from p (to (evalFormula-rename ρv ψ ν) y))))
  evalFormula-rename ρv (∀F φ) ν =
    intro
      (λ f x →
        to
          (evalFormula-cong (renameVal-liftRen-extend ρv ν x) φ)
          (to (evalFormula-rename (liftRen ρv) φ (extend x ν)) (f x)))
      (λ f x →
        from
          (evalFormula-rename (liftRen ρv) φ (extend x ν))
          (from (evalFormula-cong (renameVal-liftRen-extend ρv ν x) φ) (f x)))
  evalFormula-rename ρv (∃F φ) ν =
    intro
      (λ where
        (x , px) →
          x
          , to
              (evalFormula-cong (renameVal-liftRen-extend ρv ν x) φ)
              (to (evalFormula-rename (liftRen ρv) φ (extend x ν)) px))
      (λ where
        (x , px) →
          x
          , from
              (evalFormula-rename (liftRen ρv) φ (extend x ν))
              (from (evalFormula-cong (renameVal-liftRen-extend ρv ν x) φ) px))

  -- Weakening/substitution semantics (used by the first-order logic axioms).

  tailVal : Valuation → Valuation
  tailVal ρ n = ρ (suc n)

  insertAt : ℕ → SetU → Valuation → Valuation
  insertAt k v ρ n with cmpNat n k
  ... | less = ρ n
  ... | equal = v
  ... | greater = ρ (predNat n)

  insertAt-suc-extend
    : ∀ (k : ℕ) (v x : SetU) (ρ : Valuation)
    → ValEq (insertAt (suc k) v (extend x ρ)) (extend x (insertAt k v ρ))
  insertAt-suc-extend k v x ρ zero = refl
  insertAt-suc-extend zero v x ρ (suc zero) = refl
  insertAt-suc-extend zero v x ρ (suc (suc n)) = refl
  insertAt-suc-extend (suc k) v x ρ (suc zero) = refl
  insertAt-suc-extend (suc k) v x ρ (suc (suc n)) with cmpNat (suc n) (suc k)
  ... | less = refl
  ... | equal = refl
  ... | greater = refl

  insertAt-zero-extend
    : ∀ (v : SetU) (ρ : Valuation)
    → ValEq (insertAt zero v ρ) (extend v ρ)
  insertAt-zero-extend v ρ zero = refl
  insertAt-zero-extend v ρ (suc n) = refl

  evalTerm-lift
    : ∀ (t : Term) (ρ : Valuation) (x : SetU)
    → evalTerm (liftTerm t) (extend x ρ) ≡ evalTerm t ρ
  evalTerm-lift (var n) ρ x = refl
  evalTerm-lift emptyT ρ x = refl
  evalTerm-lift (pairT t u) ρ x =
    cong₂ pairSet (evalTerm-lift t ρ x) (evalTerm-lift u ρ x)
  evalTerm-lift (unionT t) ρ x = cong unionSet (evalTerm-lift t ρ x)
  evalTerm-lift (powerT t) ρ x = cong powersetSet (evalTerm-lift t ρ x)
  evalTerm-lift (succT t) ρ x = cong (μ SuccV) (evalTerm-lift t ρ x)
  evalTerm-lift omegaT ρ x = refl

  evalFormula-lift
    : ∀ (φ : Formula) (ρ : Valuation) (x : SetU)
    → evalFormula (liftFormula φ) (extend x ρ) ↔ evalFormula φ ρ
  evalFormula-lift φ ρ x =
    ↔-trans
      (evalFormula-rename suc φ (extend x ρ))
      (evalFormula-cong
        (λ n → refl)
        φ)

  evalTerm-substAt
    : ∀ (k : ℕ) (s t : Term) (ρ : Valuation)
    → evalTerm (substTermAt k s t) ρ ≡ evalTerm t (insertAt k (evalTerm s ρ) ρ)
  evalTerm-substAt k s (var n) ρ with cmpNat n k
  ... | less = refl
  ... | equal = refl
  ... | greater = refl
  evalTerm-substAt k s emptyT ρ = refl
  evalTerm-substAt k s (pairT t u) ρ =
    cong₂ pairSet (evalTerm-substAt k s t ρ) (evalTerm-substAt k s u ρ)
  evalTerm-substAt k s (unionT t) ρ = cong unionSet (evalTerm-substAt k s t ρ)
  evalTerm-substAt k s (powerT t) ρ = cong powersetSet (evalTerm-substAt k s t ρ)
  evalTerm-substAt k s (succT t) ρ = cong (μ SuccV) (evalTerm-substAt k s t ρ)
  evalTerm-substAt k s omegaT ρ = refl

  evalFormula-substAt
    : ∀ (k : ℕ) (s : Term) (φ : Formula) (ρ : Valuation)
    → evalFormula (substFormulaAt k s φ) ρ ↔ evalFormula φ (insertAt k (evalTerm s ρ) ρ)
  evalFormula-substAt k s ⊥F ρ = intro (λ x → x) (λ x → x)
  evalFormula-substAt k s (t ∈F u) ρ
    rewrite evalTerm-substAt k s t ρ | evalTerm-substAt k s u ρ -- rewrite-justified:evalTerm-substAt
    = intro (λ p → p) (λ p → p)
  evalFormula-substAt k s (t ≈F u) ρ
    rewrite evalTerm-substAt k s t ρ | evalTerm-substAt k s u ρ -- rewrite-justified:evalTerm-substAt
    = intro (λ p → p) (λ p → p)
  evalFormula-substAt k s (φ ⇒ ψ) ρ =
    intro
      (λ f x → to (evalFormula-substAt k s ψ ρ) (f (from (evalFormula-substAt k s φ ρ) x)))
      (λ f x → from (evalFormula-substAt k s ψ ρ) (f (to (evalFormula-substAt k s φ ρ) x)))
  evalFormula-substAt k s (φ ∧F ψ) ρ =
    intro
      (λ where
        (p , q) → to (evalFormula-substAt k s φ ρ) p , to (evalFormula-substAt k s ψ ρ) q)
      (λ where
        (p , q) → from (evalFormula-substAt k s φ ρ) p , from (evalFormula-substAt k s ψ ρ) q)
  evalFormula-substAt k s (φ ∨F ψ) ρ =
    intro
      (λ where
        (inj₁ p) → inj₁ (to (evalFormula-substAt k s φ ρ) p)
        (inj₂ q) → inj₂ (to (evalFormula-substAt k s ψ ρ) q))
      (λ where
        (inj₁ p) → inj₁ (from (evalFormula-substAt k s φ ρ) p)
        (inj₂ q) → inj₂ (from (evalFormula-substAt k s ψ ρ) q))
  evalFormula-substAt k s (φ ↔F ψ) ρ =
    intro
      (λ p →
        intro
          (λ x → to (evalFormula-substAt k s ψ ρ) (to p (from (evalFormula-substAt k s φ ρ) x)))
          (λ y → to (evalFormula-substAt k s φ ρ) (from p (from (evalFormula-substAt k s ψ ρ) y))))
      (λ p →
        intro
          (λ x → from (evalFormula-substAt k s ψ ρ) (to p (to (evalFormula-substAt k s φ ρ) x)))
          (λ y → from (evalFormula-substAt k s φ ρ) (from p (to (evalFormula-substAt k s ψ ρ) y))))
  evalFormula-substAt k s (∀F φ) ρ =
    intro to∀ from∀
    where
      v : SetU
      v = evalTerm s ρ

      to∀
        : (∀ x → evalFormula (substFormulaAt (suc k) (liftTerm s) φ) (extend x ρ))
        → (∀ x → evalFormula φ (extend x (insertAt k v ρ)))
      to∀ f x =
        to (evalFormula-cong (insertAt-suc-extend k v x ρ) φ) p1
        where
          ih = evalFormula-substAt (suc k) (liftTerm s) φ (extend x ρ)
          p0 = to ih (f x)
          p1 : evalFormula φ (insertAt (suc k) v (extend x ρ))
          p1 rewrite sym (evalTerm-lift s ρ x) -- rewrite-justified:evalTerm-lift
            = p0

      from∀
        : (∀ x → evalFormula φ (extend x (insertAt k v ρ)))
        → (∀ x → evalFormula (substFormulaAt (suc k) (liftTerm s) φ) (extend x ρ))
      from∀ f x =
        from ih p1
        where
          ih = evalFormula-substAt (suc k) (liftTerm s) φ (extend x ρ)
          p0 = from (evalFormula-cong (insertAt-suc-extend k v x ρ) φ) (f x)
          p1 : evalFormula φ (insertAt (suc k) (evalTerm (liftTerm s) (extend x ρ)) (extend x ρ))
          p1 rewrite evalTerm-lift s ρ x -- rewrite-justified:evalTerm-lift
            = p0
  evalFormula-substAt k s (∃F φ) ρ =
    intro to∃ from∃
    where
      v : SetU
      v = evalTerm s ρ

      to∃
        : Σ SetU (λ x → evalFormula (substFormulaAt (suc k) (liftTerm s) φ) (extend x ρ))
        → Σ SetU (λ x → evalFormula φ (extend x (insertAt k v ρ)))
      to∃ (x , px) =
        x
        , to
            (evalFormula-cong (insertAt-suc-extend k v x ρ) φ)
            p1
        where
          ih = evalFormula-substAt (suc k) (liftTerm s) φ (extend x ρ)
          p0 = to ih px
          p1 : evalFormula φ (insertAt (suc k) v (extend x ρ))
          p1 rewrite sym (evalTerm-lift s ρ x) -- rewrite-justified:evalTerm-lift
            = p0

      from∃
        : Σ SetU (λ x → evalFormula φ (extend x (insertAt k v ρ)))
        → Σ SetU (λ x → evalFormula (substFormulaAt (suc k) (liftTerm s) φ) (extend x ρ))
      from∃ (x , px) =
        x
        , from ih p1
        where
          ih = evalFormula-substAt (suc k) (liftTerm s) φ (extend x ρ)
          p0 = from (evalFormula-cong (insertAt-suc-extend k v x ρ) φ) px
          p1 : evalFormula φ (insertAt (suc k) (evalTerm (liftTerm s) (extend x ρ)) (extend x ρ))
          p1 rewrite evalTerm-lift s ρ x -- rewrite-justified:evalTerm-lift
            = p0
