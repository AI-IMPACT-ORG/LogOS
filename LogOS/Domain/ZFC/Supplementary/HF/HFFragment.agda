{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.Supplementary.HF.HFFragment where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥; ¬_; _↔_; intro)

-- A minimal, self-contained HF (hereditarily-finite) set model
-- with constructive proofs for a ZF fragment: Empty, Pairing, Union,
-- Extensionality (by definition), and Membership-respects-≈.

-- We intentionally avoid stdlib lists and define the small utilities we need
-- on top of the project’s `Data.List` (which bridges the host’s builtin list).

open import Data.List using (List; []; _∷_; map)

-- Minimal dependent pair and sum from project’s Data/*
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- HF sets as finite trees of lists

data HF : Set where
  ∅   : HF
  sup : List HF → HF

-- List utilities (no stdlib dependency)

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {A : Set} → List (List A) → List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

-- “Any” list membership witness

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x xs} → P x → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

Any-map : ∀ {A : Set} {P Q : A → Set} {xs : List A}
        → (∀ x → P x → Q x)
        → Any P xs → Any Q xs
Any-map f (here px) = here (f _ px)
Any-map f (there mem) = there (Any-map f mem)

-- Flip equality direction inside Any using symmetry
-- Right-to-left: from (z ≡ t) to (t ≡ z)
any-sym : ∀ {A : Set} {xs : List A} {z : A}
        → Any (λ t → z ≡ t) xs → Any (λ t → t ≡ z) xs
any-sym {xs = x ∷ xs} {z} (here e)    = here (sym e)
any-sym {xs = x ∷ xs} {z} (there pr)  = there (any-sym pr)

-- Also provide the opposite flip (t ≡ z) → (z ≡ t)
any-sym′ : ∀ {A : Set} {xs : List A} {z : A}
         → Any (λ t → t ≡ z) xs → Any (λ t → z ≡ t) xs
any-sym′ {xs = x ∷ xs} {z} (here e)    = here (sym e)
any-sym′ {xs = x ∷ xs} {z} (there pr)  = there (any-sym′ pr)

-- Membership and extensional equality

infix 4 _∈HF_ _≈HF_ _⊆HF_

_∈HF_ : HF → HF → Set
x ∈HF ∅          = ⊥
x ∈HF (sup xs)   = Any (λ y → x ≡ y) xs

_≈HF_ : HF → HF → Set
x ≈HF y = ∀ z → (z ∈HF x) ↔ (z ∈HF y)

_⊆HF_ : HF → HF → Set
x ⊆HF y = ∀ z → z ∈HF x → z ∈HF y

refl≈HF  : ∀ x → x ≈HF x
refl≈HF x z = intro (λ p → p) (λ p → p)

sym≈HF   : ∀ {x y} → x ≈HF y → y ≈HF x
sym≈HF e z = intro (λ p → _↔_.from (e z) p) (λ p → _↔_.to (e z) p)

trans≈HF : ∀ {x y z} → x ≈HF y → y ≈HF z → x ≈HF z
trans≈HF e₁ e₂ w = intro (λ p → _↔_.to (e₂ w) (_↔_.to (e₁ w) p))
                          (λ p → _↔_.from (e₁ w) (_↔_.from (e₂ w) p))

refl⊆HF : ∀ x → x ⊆HF x
refl⊆HF x z zx = zx

trans⊆HF : ∀ {x y z} → x ⊆HF y → y ⊆HF z → x ⊆HF z
trans⊆HF xy yz z mem = yz z (xy z mem)

-- Basic constructors and helpers

emptyHF : HF
emptyHF = ∅

pairHF : HF → HF → HF
pairHF x y = sup (x ∷ y ∷ [])

contents : HF → List HF
contents ∅         = []
contents (sup xs)  = xs

unionHF : HF → HF
unionHF ∅         = ∅
unionHF (sup xs)  = sup (concat (map contents xs))

addPairs : HF → List HF → List HF
addPairs x [] = []
addPairs x (y ∷ ys) = pairHF x y ∷ addPairs x ys

pairsList : List HF → List HF
pairsList [] = []
pairsList (x ∷ xs) = addPairs x xs ++ pairsList xs

-- Insert a single element into a set (multiset-style; duplicates allowed).

insertHF : HF → HF → HF
insertHF x ∅         = sup (x ∷ [])
insertHF x (sup xs)  = sup (x ∷ xs)

-- Membership helpers for insertHF: we only need the inclusion-style lemmas.

insertHF-infl : ∀ x c → c ⊆HF insertHF x c
insertHF-infl x ∅ z ()
insertHF-infl x (sup xs) z mem = there mem

insertHF-mono : ∀ x c d → c ⊆HF d → insertHF x c ⊆HF insertHF x d
insertHF-mono x ∅ ∅ c⊆d z (here zx) = here zx
insertHF-mono x ∅ ∅ c⊆d z (there ())
insertHF-mono x ∅ (sup ys) c⊆d z (here zx) = here zx
insertHF-mono x ∅ (sup ys) c⊆d z (there ())
insertHF-mono x (sup xs) ∅ c⊆d z (here zx) = here zx
insertHF-mono x (sup xs) ∅ c⊆d z (there mem) with c⊆d z mem
... | ()
insertHF-mono x (sup xs) (sup ys) c⊆d z (here zx) = here zx
insertHF-mono x (sup xs) (sup ys) c⊆d z (there mem) =
  insertHF-infl x (sup ys) z (c⊆d z mem)

insertHF-idem : ∀ x c → insertHF x (insertHF x c) ⊆HF insertHF x c
insertHF-idem x ∅ z (here zx) = here zx
insertHF-idem x ∅ z (there mem) = mem
insertHF-idem x (sup xs) z (here zx) = here zx
insertHF-idem x (sup xs) z (there mem) = mem

insertHF-self≤ : ∀ x c → insertHF x c ⊆HF insertHF x (insertHF x c)
insertHF-self≤ x ∅ z (here zx) = here zx
insertHF-self≤ x ∅ z (there ())
insertHF-self≤ x (sup xs) z (here zx) = here zx
insertHF-self≤ x (sup xs) z (there mem) =
  there (insertHF-infl x (sup xs) z mem)

insertHF-stable : ∀ x c → x ∈HF c → insertHF x c ⊆HF c
insertHF-stable x ∅ ()
insertHF-stable x (sup xs) x∈ z (here zx) =
  Any-map (λ _ eq → trans zx eq) x∈
insertHF-stable x (sup xs) x∈ z (there mem) = mem

ensureEmptyHF : HF → HF
ensureEmptyHF = insertHF emptyHF

ensureEmpty-infl : ∀ c → c ⊆HF ensureEmptyHF c
ensureEmpty-infl = insertHF-infl emptyHF

ensureEmpty-mono : ∀ {c d} → c ⊆HF d → ensureEmptyHF c ⊆HF ensureEmptyHF d
ensureEmpty-mono {c} {d} = insertHF-mono emptyHF c d

ensureEmpty-idem : ∀ c → ensureEmptyHF (ensureEmptyHF c) ⊆HF ensureEmptyHF c
ensureEmpty-idem = insertHF-idem emptyHF

ensureEmpty-self≤ : ∀ c → ensureEmptyHF c ⊆HF ensureEmptyHF (ensureEmptyHF c)
ensureEmpty-self≤ = insertHF-self≤ emptyHF

ensureEmpty-has-empty : ∀ c → emptyHF ∈HF ensureEmptyHF c
ensureEmpty-has-empty ∅ = here refl
ensureEmpty-has-empty (sup xs) = here refl

ensureEmpty-stable : ∀ c → emptyHF ∈HF c → ensureEmptyHF c ⊆HF c
ensureEmpty-stable = insertHF-stable emptyHF

-- Sum split/append lemmas for Any

split-append : ∀ {A : Set} {P : A → Set} {xs ys : List A}
  → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
split-append {xs = []} {ys} mem = inj₂ mem
split-append {xs = x ∷ xs} {ys} (here px) = inj₁ (here px)
split-append {xs = x ∷ xs} {ys} (there mem) with split-append {xs = xs} {ys = ys} mem
... | inj₁ memL = inj₁ (there memL)
... | inj₂ memR = inj₂ memR

append-left : ∀ {A : Set} {P : A → Set} {xs ys : List A}
            → Any P xs → Any P (xs ++ ys)
append-left {xs = []} ()
append-left {xs = x ∷ xs} {ys} (here px) = here px
append-left {xs = x ∷ xs} {ys} (there mem) =
  there (append-left {xs = xs} {ys = ys} mem)

append-right : ∀ {A : Set} {P : A → Set} {xs ys : List A}
             → Any P ys → Any P (xs ++ ys)
append-right {xs = []} mem = mem
append-right {xs = x ∷ xs} mem =
  there (append-right {xs = xs} mem)


-- Empty axiom: no element in ∅

empty-axiom : Σ HF (λ e → ∀ z → ¬ (z ∈HF e))
empty-axiom = emptyHF , (λ z → λ ())

-- Pairing axiom: z ∈ {x,y} ↔ (z ≡ x) ⊎ (z ≡ y)

pairing-axiom : ∀ x y → Σ HF (λ p → ∀ z → (z ∈HF p) ↔ ((z ≡ x) ⊎ (z ≡ y)))
pairing-axiom x y =
  let p = pairHF x y in
  p , λ z →
    intro
      (λ where
         (here zx)               → inj₁ zx
         (there (here zy))       → inj₂ zy
         (there (there ()))
      )
      (λ where
         (inj₁ zx) → here zx
         (inj₂ zy) → there (here zy)
      )

-- Union axiom: z ∈ ⋃x ↔ ∃y ∈ x. z ∈ y

union-axiom : ∀ x → Σ HF (λ u → ∀ z → (z ∈HF u) ↔ (Σ HF (λ y → (y ∈HF x) × (z ∈HF y))))
union-axiom ∅ = ∅ , λ z → intro (λ ()) (λ { (_ , ((), _)) })
union-axiom (sup xs) = unionHF (sup xs) , λ z →
  intro
    (λ mem →
       let (y , pair)    = locate xs z mem
           (yin , zin) = pair
       in y , (yin , contents→∈ y z zin))
    (λ { (y , (yin , zin)) → spread xs y z yin (∈→contents y z zin) })
  where
    locate : (xs : List HF) → (z : HF)
           → Any (λ t → z ≡ t) (concat (map contents xs))
           → Σ HF (λ y → Any (λ t → y ≡ t) xs × Any (λ t → z ≡ t) (contents y))
    locate [] z ()
    locate (y ∷ ys) z mem with split-append {xs = contents y} {ys = concat (map contents ys)} mem
    ... | inj₁ memY = y , (here refl , memY)
    ... | inj₂ memRest with locate ys z memRest
    ... | (y' , (inYs , inY')) = y' , (there inYs , inY')

    spread : (xs : List HF) → (y z : HF)
           → Any (λ t → y ≡ t) xs
           → Any (λ t → z ≡ t) (contents y)
           → Any (λ t → z ≡ t) (concat (map contents xs))
    spread [] y z () _
    spread (x ∷ xs) y z (here py) zin =
      append-left {xs = contents x} {ys = concat (map contents xs)}
        (subst (λ u → Any (λ t → z ≡ t) (contents u)) py zin)
    spread (x ∷ xs) y z (there yin) zin =
      append-right {xs = contents x} (spread xs y z yin zin)

    contents→∈ : ∀ y z → Any (λ t → z ≡ t) (contents y) → z ∈HF y
    contents→∈ ∅ z ()
    contents→∈ (sup ys) z zin = zin

    ∈→contents : ∀ y z → z ∈HF y → Any (λ t → z ≡ t) (contents y)
    ∈→contents ∅ z ()
    ∈→contents (sup ys) z zin = zin

-- Extensionality axiom: already definitional under _≈HF_.

extensionalityHF : ∀ x y → (∀ z → (z ∈HF x) ↔ (z ∈HF y)) → x ≈HF y
extensionalityHF x y e = e

-- Membership respects extensional equality

mem-ext-HF : ∀ {x y} → x ≈HF y → ∀ z → (z ∈HF x) ↔ (z ∈HF y)
mem-ext-HF e z = e z

-- A small ZF fragment pack (self-contained, kernel-free)

record ZFFrag : Set₁ where
  infix 4 _∈_ _≈_
  field
    SetU   : Set
    _∈_    : SetU → SetU → Set
    _≈_    : SetU → SetU → Set
    refl≈  : ∀ x → x ≈ x
    sym≈   : ∀ {x y} → x ≈ y → y ≈ x
    trans≈ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    extensionality : ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≈ y
    mem-ext        : ∀ {x y} → x ≈ y → ∀ z → (z ∈ x) ↔ (z ∈ y)

    empty   : Σ SetU (λ e → ∀ z → ¬ (z ∈ e))
    pairing : ∀ x y → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ ((z ≡ x) ⊎ (z ≡ y)))
    union   : ∀ x → Σ SetU (λ u → ∀ z → (z ∈ u) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y))))

HFFrag : ZFFrag
HFFrag = record
  { SetU   = HF
  ; _∈_    = _∈HF_
  ; _≈_    = _≈HF_
  ; refl≈  = refl≈HF
  ; sym≈   = sym≈HF
  ; trans≈ = trans≈HF
  ; extensionality = extensionalityHF
  ; mem-ext = mem-ext-HF
  ; empty   = empty-axiom
  ; pairing = pairing-axiom
  ; union   = union-axiom
  }
