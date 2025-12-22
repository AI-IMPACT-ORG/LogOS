{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Logic.ZFC.Axioms where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; intro; ⊥; ⊥-elim)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import Data.Fin using (Fin; fzero; fsuc)
open import Data.Product using (Σ; _,_; _×_; fst; snd)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Domain.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.Logic.FOL.All as FOL
open import LogOS.Logic.ZFC.Signature

-- ZF(ZFC) axioms as FOL sentences, plus a “validity in any ZF pack” theorem.
--
-- This is intentionally “semantic”: we map the existing `ZFAxiomsᶠ` interface
-- to a concrete first-order interpretation, then state the axiom sentences in
-- that language and prove they are valid.

module FromZFAxiomsᶠ {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K   : Kernel Sig Q)
                     (zf  : ZFAxiomsᶠ K)
                     where
  open Kernel K
  open ZFAxiomsᶠ zf
  open LogOS.Logic.ZFC.Signature.ForKernel K

  -- Shorthands for the ZFC-style signature and its atomic formulas.

  ΣZ : FOL.Signature {ℓ}
  ΣZ = ΣZFC

  infix 4 _∈ᶠ_ _≈ᶠ_

  _∈ᶠ_ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  x ∈ᶠ y = FOL.rel₂ mem x y

  _≈ᶠ_ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  x ≈ᶠ y = FOL.rel₂ eq x y

  Predᶠ : ∀ {n} → Code → FOL.Term n → FOL.Fml ΣZ n
  Predᶠ φ x = FOL.pred φ x

  Relᶠ : ∀ {n} → Code → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  Relᶠ ψ x y = FOL.rel₂ (rel ψ) x y

  -- de Bruijn helpers

  v0 : ∀ {n} → FOL.Term (suc n)
  v0 = fzero

  v1 : ∀ {n} → FOL.Term (suc (suc n))
  v1 = fsuc fzero

  v2 : ∀ {n} → FOL.Term (suc (suc (suc n)))
  v2 = fsuc (fsuc fzero)

  v3 : ∀ {n} → FOL.Term (suc (suc (suc (suc n))))
  v3 = fsuc (fsuc (fsuc fzero))

  -- Interpretation of the ZFC signature in the given ZF pack.

  RelI : ZRel₂ → SetU → SetU → Set ℓ
  RelI mem      x y = x ∈ y
  RelI eq       x y = x ≈ y
  RelI (rel ψ)  x y = Rel ψ x y

  module Sem = FOL.For {Σ₀ = ΣZ} SetU Pred RelI
  open Sem

  -- ==========================================================================
  -- Pure {∈,≈} macros used by Infinity/Foundation.
  -- ==========================================================================

  IsEmpty : ∀ {n} → FOL.Term n → FOL.Fml ΣZ n
  IsEmpty x =
    FOL.All (FOL.Not (v0 ∈ᶠ fsuc x))

  -- `IsSucc x y` means: y = x ∪ {x}, characterised purely by membership.
  IsSucc : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  IsSucc x y =
    FOL.All
      (FOL.Iff
        (v0 ∈ᶠ fsuc y)
        ((v0 ∈ᶠ fsuc x) FOL.∨ (v0 ≈ᶠ fsuc x)))

  -- ==========================================================================
  -- ZF axiom sentences (schematic over `Code` for Separation/Replacement).
  -- ==========================================================================

  -- Equality axioms for the interpreted relation `eq` (i.e. `_≈_`).

  EqReflᶠ : FOL.Fml ΣZ 0
  EqReflᶠ = FOL.All (v0 ≈ᶠ v0)

  EqSymᶠ : FOL.Fml ΣZ 0
  EqSymᶠ =
    FOL.All (FOL.All ((v1 ≈ᶠ v0) FOL.⇒ (v0 ≈ᶠ v1)))

  EqTransᶠ : FOL.Fml ΣZ 0
  EqTransᶠ =
    FOL.All (FOL.All (FOL.All
      (((v2 ≈ᶠ v1) FOL.∧ (v1 ≈ᶠ v0)) FOL.⇒ (v2 ≈ᶠ v0))))

  -- Right congruence of membership with respect to `≈` (available as `mem-ext`).
  MemCongRᶠ : FOL.Fml ΣZ 0
  MemCongRᶠ =
    FOL.All (FOL.All
      ((v1 ≈ᶠ v0) FOL.⇒ (FOL.All (FOL.Iff (v0 ∈ᶠ v2) (v0 ∈ᶠ v1)))))

  -- Left congruence of membership with respect to `≈` (available as `mem-congL`).
  MemCongLᶠ : FOL.Fml ΣZ 0
  MemCongLᶠ =
    FOL.All (FOL.All
      ((v1 ≈ᶠ v0) FOL.⇒ (FOL.All (FOL.Iff (v2 ∈ᶠ v0) (v1 ∈ᶠ v0)))))

  Extensionalityᶠ : FOL.Fml ΣZ 0
  Extensionalityᶠ =
    FOL.All (FOL.All
      ((FOL.All (FOL.Iff (v0 ∈ᶠ v2) (v0 ∈ᶠ v1)))
        FOL.⇒ (v1 ≈ᶠ v0)))

  Emptyᶠ : FOL.Fml ΣZ 0
  Emptyᶠ =
    FOL.Ex (FOL.All (FOL.Not (v0 ∈ᶠ v1)))

  Pairingᶠ : FOL.Fml ΣZ 0
  Pairingᶠ =
    FOL.All (FOL.All
      (FOL.Ex (FOL.All
        (FOL.Iff
          (v0 ∈ᶠ v1)
          ((v0 ≈ᶠ v3) FOL.∨ (v0 ≈ᶠ v2))))))

  Unionᶠ : FOL.Fml ΣZ 0
  Unionᶠ =
    FOL.All
      (FOL.Ex (FOL.All
        (FOL.Iff
          (v0 ∈ᶠ v1)
          (FOL.Ex ((v0 ∈ᶠ v3) FOL.∧ (v1 ∈ᶠ v0))))))

  Powersetᶠ : FOL.Fml ΣZ 0
  Powersetᶠ =
    FOL.All
      (FOL.Ex (FOL.All
        (FOL.Iff
          (v0 ∈ᶠ v1)
          (FOL.All ((v0 ∈ᶠ v1) FOL.⇒ (v0 ∈ᶠ v3))))))

  Infinityᶠ : FOL.Fml ΣZ 0
  Infinityᶠ =
    FOL.Ex (FOL.Ex
      ( IsEmpty v0
        FOL.∧ ((v0 ∈ᶠ v1)
        FOL.∧ (FOL.All
          ((v0 ∈ᶠ v2)
            FOL.⇒ (FOL.Ex (IsSucc v1 v0 FOL.∧ (v0 ∈ᶠ v3))))))))

  Foundationᶠ : FOL.Fml ΣZ 0
  Foundationᶠ =
    FOL.All
      ( IsEmpty v0
        FOL.∨ (FOL.Ex
          ((v0 ∈ᶠ v1)
            FOL.∧ (FOL.All ((v0 ∈ᶠ v2) FOL.⇒ (FOL.Not (v0 ∈ᶠ v1)))))) )

  Separationᶠ : Code → FOL.Fml ΣZ 0
  Separationᶠ φ =
    FOL.All
      (FOL.Ex (FOL.All
        (FOL.Iff
          (v0 ∈ᶠ v1)
          ((v0 ∈ᶠ v2) FOL.∧ Predᶠ φ v0))))

  -- Replacement is stated as: if the coded relation is functional (single-valued,
  -- up to `≈`), then its image exists.

  Functionalᶠ : Code → FOL.Fml ΣZ 0
  Functionalᶠ ψ =
    FOL.All (FOL.All (FOL.All
      (((Relᶠ ψ v2 v1) FOL.∧ (Relᶠ ψ v2 v0)) FOL.⇒ (v1 ≈ᶠ v0))))

  ReplacementBodyᶠ : Code → FOL.Fml ΣZ 0
  ReplacementBodyᶠ ψ =
    FOL.All
      (FOL.Ex (FOL.All
        (FOL.Iff
          (v0 ∈ᶠ v1)
          (FOL.Ex ((v0 ∈ᶠ v3) FOL.∧ Relᶠ ψ v0 v1)))))

  Replacementᶠ : Code → FOL.Fml ΣZ 0
  Replacementᶠ ψ =
    (Functionalᶠ ψ) FOL.⇒ (ReplacementBodyᶠ ψ)

  -- See also: `ZFAxiomsᶠ.foundation` (semantic form, relative to `zeroS`).

  -- ==========================================================================
  -- Validity: every ZF pack satisfies the corresponding axiom sentences.
  -- ==========================================================================

  valid-EqReflᶠ : ∀ env → Sat env EqReflᶠ
  valid-EqReflᶠ env x = refl≈ x

  valid-EqSymᶠ : ∀ env → Sat env EqSymᶠ
  valid-EqSymᶠ env x y x≈y = sym≈ x≈y

  valid-EqTransᶠ : ∀ env → Sat env EqTransᶠ
  valid-EqTransᶠ env x y z (x≈y , y≈z) = trans≈ x≈y y≈z

  valid-MemCongRᶠ : ∀ env → Sat env MemCongRᶠ
  valid-MemCongRᶠ env x y x≈y z =
    let spec = mem-ext x≈y z
    in (Prop.to spec , Prop.from spec)

  valid-MemCongLᶠ : ∀ env → Sat env MemCongLᶠ
  valid-MemCongLᶠ env x y x≈y z =
    let spec = mem-congL x≈y z
    in (Prop.to spec , Prop.from spec)

  valid-Extensionalityᶠ : ∀ env → Sat env Extensionalityᶠ
  valid-Extensionalityᶠ env x y h =
    extensionality x y (λ z → intro (fst (h z)) (snd (h z)))

  valid-Emptyᶠ : ∀ env → Sat env Emptyᶠ
  valid-Emptyᶠ env =
    let e   = proj₁ empty
        nz  = proj₂ empty
    in e , (λ z → (λ memz → ⊥-elim (nz z memz)))

  valid-Pairingᶠ : ∀ env → Sat env Pairingᶠ
  valid-Pairingᶠ env x y =
    let p    = proj₁ (pairing x y)
        spec = proj₂ (pairing x y)
    in p , (λ z → (Prop.to (spec z) , Prop.from (spec z)))

  valid-Unionᶠ : ∀ env → Sat env Unionᶠ
  valid-Unionᶠ env x =
    let u    = proj₁ (union x)
        spec = proj₂ (union x)
    in u , (λ z →
      ( (λ memz →
          let y  = proj₁ (Prop.to (spec z) memz)
              py = proj₂ (Prop.to (spec z) memz)
          in y , (fst py , snd py))
      , (λ where
          (y , (yx , zy)) →
            Prop.from (spec z) (y , (yx , zy)) )))

  valid-Powersetᶠ : ∀ env → Sat env Powersetᶠ
  valid-Powersetᶠ env x =
    let p    = proj₁ (powerset x)
        spec = proj₂ (powerset x)
    in p , (λ z → (Prop.to (spec z) , Prop.from (spec z)))

  valid-Infinityᶠ : ∀ env → Sat env Infinityᶠ
  valid-Infinityᶠ env =
    let
      ω    = proj₁ infinity
      spec = proj₂ infinity

      ρ₂ = extend zeroS (extend ω env)

      isEmpty : Sat ρ₂ (IsEmpty {n = 2} v0)
      isEmpty z memz = ⊥-elim (zeroS-empty z memz)

      zeroS∈ω : Sat ρ₂ (v0 ∈ᶠ v1)
      zeroS∈ω = Prop.from (spec zeroS) (inj₁ (refl≈ zeroS))

      closed
        : Sat ρ₂ (FOL.All ((v0 ∈ᶠ v2) FOL.⇒ (FOL.Ex (IsSucc v1 v0 FOL.∧ (v0 ∈ᶠ v3)))))
      closed y y∈ω =
        succ y
        , ( (λ t → (Prop.to (mem-succ↔ y t) , Prop.from (mem-succ↔ y t)))
          , Prop.from (spec (succ y)) (inj₂ (y , (y∈ω , refl≈ (succ y)))) )

    in
    ω , (zeroS , (isEmpty , (zeroS∈ω , closed)))

  valid-Foundationᶠ : ∀ env → Sat env Foundationᶠ
  valid-Foundationᶠ env x with foundation x
  ... | inj₁ x≈0 =
    inj₁ (λ z memz →
      let mem0 = Prop.to (mem-ext x≈0 z) memz
      in ⊥-elim (zeroS-empty z mem0))
  ... | inj₂ (y , (y∈x , min)) =
    inj₂ (y , (y∈x , (λ z z∈x z∈y → ⊥-elim (min z z∈x z∈y))))

  valid-Separationᶠ : ∀ φ env → Sat env (Separationᶠ φ)
  valid-Separationᶠ φ env x =
    let y    = proj₁ (separationᶠ φ x)
        spec = proj₂ (separationᶠ φ x)
    in y , (λ z → (Prop.to (spec z) , Prop.from (spec z)))

  valid-ReplacementBodyᶠ
    : ∀ ψ → FunctionalRel (Rel ψ) → ∀ env → Sat env (ReplacementBodyᶠ ψ)
  valid-ReplacementBodyᶠ ψ fun env x =
    let y    = proj₁ (replacementᶠ ψ fun x)
        spec = proj₂ (replacementᶠ ψ fun x)
    in y , (λ z → (Prop.to (spec z) , Prop.from (spec z)))

  functionalRel-from-Sat
    : ∀ ψ env → Sat env (Functionalᶠ ψ) → FunctionalRel (Rel ψ)
  functionalRel-from-Sat ψ env satFun u z₁ z₂ ru₁ ru₂ =
    satFun u z₁ z₂ (ru₁ , ru₂)

  valid-Replacementᶠ : ∀ ψ env → Sat env (Replacementᶠ ψ)
  valid-Replacementᶠ ψ env satFun =
    valid-ReplacementBodyᶠ ψ (functionalRel-from-Sat ψ env satFun) env

-- ZFC extension: internalise the Axiom of Choice as a single FOL sentence,
-- validated in any `ZFCAxiomsᶠ` pack.

module FromZFCAxiomsᶠ {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K   : Kernel Sig Q)
                     (zfc : ZFCAxiomsᶠ K)
                     where
  open Kernel K
  open ZFCAxiomsᶠ zfc

  module ZF = FromZFAxiomsᶠ K zf
  open ZF public
  open ZF.Sem

  -- Abbreviations matching `LogOS.Domain.SetTheory.ChoiceAxiom`.
  pairSet : SetU → SetU → SetU
  pairSet x y = proj₁ (pairing x y)

  singleton : SetU → SetU
  singleton x = pairSet x x

  opair : SetU → SetU → SetU
  opair x y = pairSet (singleton x) (pairSet x y)

  GraphSet : SetU → SetU → SetU → Set ℓ
  GraphSet f x y = opair x y ∈ f

  elim⊎ : ∀ {A : Set ℓ} → (A ⊎ A) → A
  elim⊎ (inj₁ a) = a
  elim⊎ (inj₂ a) = a

  -- ------------------------------------------------------------------------
  -- Pure {∈,≈} macros for Choice
  -- ------------------------------------------------------------------------

  -- Unordered pair witness: `p = {x,y}` by membership.
  PairOfᶠ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  PairOfᶠ x y p =
    FOL.All
      (FOL.Iff
        (v0 ∈ᶠ fsuc p)
        ((v0 ≈ᶠ fsuc x) FOL.∨ (v0 ≈ᶠ fsuc y)))

  SingletonOfᶠ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  SingletonOfᶠ x s =
    FOL.All
      (FOL.Iff
        (v0 ∈ᶠ fsuc s)
        (v0 ≈ᶠ fsuc x))

  -- Kuratowski ordered pair witness: `o = ⟨x,y⟩ = {{x},{x,y}}`.
  OPairOfᶠ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  OPairOfᶠ x y o =
    FOL.Ex (FOL.Ex
      ( (SingletonOfᶠ (fsuc (fsuc x)) v1)
        FOL.∧ (PairOfᶠ (fsuc (fsuc x)) (fsuc (fsuc y)) v0)
        FOL.∧ (PairOfᶠ v1 v0 (fsuc (fsuc o))) ))

  -- Graph membership via an ordered pair witness.
  GraphSetᶠ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  GraphSetᶠ f x y =
    FOL.Ex
      ( (OPairOfᶠ (fsuc x) (fsuc y) v0)
        FOL.∧ (v0 ∈ᶠ fsuc f))

  -- A family X of nonempty sets.
  NonemptyFamilyᶠ : ∀ {n} → FOL.Term n → FOL.Fml ΣZ n
  NonemptyFamilyᶠ X =
    FOL.All ((v0 ∈ᶠ fsuc X) FOL.⇒ (FOL.Ex (v0 ∈ᶠ v1)))

  DomContainedᶠ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  DomContainedᶠ f X =
    FOL.All (FOL.All
      ((GraphSetᶠ (fsuc (fsuc f)) v1 v0) FOL.⇒ (v1 ∈ᶠ fsuc (fsuc X))))

  TotalOnᶠ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  TotalOnᶠ f X =
    FOL.All
      ((v0 ∈ᶠ fsuc X)
        FOL.⇒ (FOL.Ex ((GraphSetᶠ (fsuc (fsuc f)) v1 v0) FOL.∧ (v0 ∈ᶠ v1))))

  FunctionalOnᶠ : ∀ {n} → FOL.Term n → FOL.Fml ΣZ n
  FunctionalOnᶠ f =
    FOL.All (FOL.All (FOL.All
      (((GraphSetᶠ (fsuc (fsuc (fsuc f))) v2 v1) FOL.∧ (GraphSetᶠ (fsuc (fsuc (fsuc f))) v2 v0))
        FOL.⇒ (v1 ≈ᶠ v0))))

  ChoiceFunctionOnᶠ : ∀ {n} → FOL.Term n → FOL.Term n → FOL.Fml ΣZ n
  ChoiceFunctionOnᶠ f X =
    (DomContainedᶠ f X) FOL.∧ ((TotalOnᶠ f X) FOL.∧ (FunctionalOnᶠ f))

  Choiceᶠ : FOL.Fml ΣZ 0
  Choiceᶠ =
    FOL.All
      ((NonemptyFamilyᶠ v0)
        FOL.⇒ (FOL.Ex (ChoiceFunctionOnᶠ v0 v1)))

  -- ------------------------------------------------------------------------
  -- Validity proof
  -- ------------------------------------------------------------------------

  pairSet-from-PairOfᶠ
    : ∀ {n} (env : Env n) (x y p : FOL.Term n)
    → Sat env (PairOfᶠ x y p)
    → env p ≈ pairSet (env x) (env y)
  pairSet-from-PairOfᶠ env x y p satPair =
    let
      canon = pairing (env x) (env y)
      pxy   = pairSet (env x) (env y)
      specP : ∀ z → (z ∈ env p) ↔ ((z ≈ env x) ⊎ (z ≈ env y))
      specP z = intro (fst (satPair z)) (snd (satPair z))

      specC = proj₂ canon

      membEq : ∀ z → (z ∈ env p) ↔ (z ∈ pxy)
      membEq z =
        intro
          (λ z∈p →
            let disj = Prop.to (specP z) z∈p
            in Prop.from (specC z) disj)
          (λ z∈pxy →
            let disj = Prop.to (specC z) z∈pxy
            in Prop.from (specP z) disj)

    in
    extensionality (env p) pxy membEq

  singleton-from-SingletonOfᶠ
    : ∀ {n} (env : Env n) (x s : FOL.Term n)
    → Sat env (SingletonOfᶠ x s)
    → env s ≈ singleton (env x)
  singleton-from-SingletonOfᶠ env x s satSing =
    let
      canon = pairing (env x) (env x)
      sx    = singleton (env x)

      specS : ∀ z → (z ∈ env s) ↔ (z ≈ env x)
      specS z = intro (fst (satSing z)) (snd (satSing z))

      specC : ∀ z → (z ∈ sx) ↔ ((z ≈ env x) ⊎ (z ≈ env x))
      specC = proj₂ canon

      membEq : ∀ z → (z ∈ env s) ↔ (z ∈ sx)
      membEq z =
        intro
          (λ z∈s →
            let zx = Prop.to (specS z) z∈s
            in Prop.from (specC z) (inj₁ zx))
          (λ z∈sx →
            let disj = Prop.to (specC z) z∈sx
                zx = elim disj
            in Prop.from (specS z) zx)

    in
    extensionality (env s) sx membEq
    where
      elim : ∀ {A : Set ℓ} → (A ⊎ A) → A
      elim (inj₁ a) = a
      elim (inj₂ a) = a

  opair-from-OPairOfᶠ
    : ∀ {n} (env : Env n) (x y o : FOL.Term n)
    → Sat env (OPairOfᶠ x y o)
    → env o ≈ opair (env x) (env y)
  opair-from-OPairOfᶠ {n} env x y o (s , (p , (satS , (satP , satO)))) =
    let
      env₂ : Env (suc (suc n))
      env₂ = extend p (extend s env)

      -- Extract the three membership characterisations.
      s≈ : s ≈ singleton (env x)
      s≈ =
        singleton-from-SingletonOfᶠ env₂ (fsuc (fsuc x)) v1
          (λ z → satS z)

      p≈ : p ≈ pairSet (env x) (env y)
      p≈ =
        pairSet-from-PairOfᶠ env₂ (fsuc (fsuc x)) (fsuc (fsuc y)) v0
          (λ z → satP z)

      oCanon = opair (env x) (env y)

      o≈ : env o ≈ oCanon
      o≈ =
        let
          canon = pairing (singleton (env x)) (pairSet (env x) (env y))
          specC = proj₂ canon

          specO : ∀ z → (z ∈ env o) ↔ ((z ≈ s) ⊎ (z ≈ p))
          specO = λ z → intro (fst (satO z)) (snd (satO z))

          toCanon : ∀ z → (z ≈ s) ⊎ (z ≈ p) → z ∈ oCanon
          toCanon = λ z →
            λ
              { (inj₁ z≈s') → Prop.from (specC z) (inj₁ (trans≈ z≈s' s≈))
              ; (inj₂ z≈p') → Prop.from (specC z) (inj₂ (trans≈ z≈p' p≈))
              }

          fromCanon
            : ∀ z
            → (z ≈ singleton (env x)) ⊎ (z ≈ pairSet (env x) (env y))
            → (z ≈ s) ⊎ (z ≈ p)
          fromCanon = λ z →
            λ
              { (inj₁ z≈sx)  → inj₁ (trans≈ z≈sx (sym≈ s≈))
              ; (inj₂ z≈pxy) → inj₂ (trans≈ z≈pxy (sym≈ p≈))
              }

          membEq : ∀ z → (z ∈ env o) ↔ (z ∈ oCanon)
          membEq = λ z →
            intro
              (λ z∈o → toCanon z (Prop.to (specO z) z∈o))
              (λ z∈op →
                Prop.from (specO z) (fromCanon z (Prop.to (specC z) z∈op)))

        in
        extensionality (env o) oCanon membEq

    in
    o≈

  sat-GraphSetᶠ-from-GraphSet
    : ∀ {n} (env : Env n) (f x y : FOL.Term n)
    → GraphSet (env f) (env x) (env y)
    → Sat env (GraphSetᶠ f x y)
  sat-GraphSetᶠ-from-GraphSet env f x y gxy =
    let
      o    = opair (env x) (env y)
      env₁ = extend o env

      o∈f : Sat env₁ (v0 ∈ᶠ fsuc f)
      o∈f = gxy

      satOP : Sat env₁ (OPairOfᶠ (fsuc x) (fsuc y) v0)
      satOP =
        let
          sx  = singleton (env x)
          pxy = pairSet (env x) (env y)
        in
        sx
        , (pxy
        , ( (λ z →
              let spec = proj₂ (pairing (env x) (env x)) z
              in ( (λ z∈sx' → elim⊎ (Prop.to spec z∈sx'))
                 , (λ z≈x → Prop.from spec (inj₁ z≈x)) ))
          , ( (λ z →
                let spec = proj₂ (pairing (env x) (env y)) z
                in (Prop.to spec , Prop.from spec))
            , (λ z →
                let spec = proj₂ (pairing sx pxy) z
                in (Prop.to spec , Prop.from spec)) )))

    in
    o , ((satOP , o∈f))

  GraphSet-from-Sat-GraphSetᶠ
    : ∀ {n} (env : Env n) (f x y : FOL.Term n)
    → Sat env (GraphSetᶠ f x y)
    → GraphSet (env f) (env x) (env y)
  GraphSet-from-Sat-GraphSetᶠ env f x y (o , (satOP , o∈f)) =
    let
      o≈ = opair-from-OPairOfᶠ (extend o env) (fsuc x) (fsuc y) v0 satOP
      spec = mem-congL o≈ (env f)
    in
    Prop.to spec o∈f

  valid-Choiceᶠ : ∀ env → Sat env Choiceᶠ
  valid-Choiceᶠ env X satNonempty =
    let
      nonempty : ∀ x → x ∈ X → Σ SetU (λ y → y ∈ x)
      nonempty =
        λ x x∈X →
          let satImp = satNonempty x
              (y , y∈x) = satImp x∈X
          in y , y∈x

      fWitness = AC X nonempty
      f = proj₁ fWitness
      dom = fst (proj₂ fWitness)
      tot = fst (snd (proj₂ fWitness))
      fun = snd (snd (proj₂ fWitness))

      envXF : Env 2
      envXF = extend f (extend X env)

      satDom : Sat envXF (DomContainedᶠ v0 v1)
      satDom =
        λ x y satG →
          let envXY = extend y (extend x envXF)
              gxy   = GraphSet-from-Sat-GraphSetᶠ envXY (fsuc (fsuc v0)) v1 v0 satG
          in dom x y gxy

      satTot : Sat envXF (TotalOnᶠ v0 v1)
      satTot =
        λ x x∈X →
          let (y , (gxy , y∈x)) = tot x x∈X
              envXY = extend y (extend x envXF)
          in y , (sat-GraphSetᶠ-from-GraphSet envXY (fsuc (fsuc v0)) v1 v0 gxy , y∈x)

      satFun : Sat envXF (FunctionalOnᶠ v0)
      satFun =
        λ x y₁ y₂ (satG₁ , satG₂) →
          let envXYZ = extend y₂ (extend y₁ (extend x envXF))
              g₁ = GraphSet-from-Sat-GraphSetᶠ envXYZ (fsuc (fsuc (fsuc v0))) v2 v1 satG₁
              g₂ = GraphSet-from-Sat-GraphSetᶠ envXYZ (fsuc (fsuc (fsuc v0))) v2 v0 satG₂
          in fun x y₁ y₂ g₁ g₂

    in
    f , (satDom , (satTot , satFun))
