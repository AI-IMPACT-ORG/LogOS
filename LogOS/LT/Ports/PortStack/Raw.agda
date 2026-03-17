{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack.Raw where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Explicit raw/shadowing stack lane.
--
-- This module keeps the duplicate-tag, leftmost-resolution machinery reachable
-- for internal architecture work. Curated public surfaces should prefer the
-- uniqueness-first facade in `LogOS.LT.Ports.PortStack`.

open import LogOS.Prelude

open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; idThin2Functor; _∘F_)
open import LogOS.LT.Thin2Functor.Strictification using (StrictThin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; Ob
  ; HomD
  ; DecoratedObj
  ; DecoratedHom
  ; DecoratedThin2Cat
  ; mkTotalObjR
  ; mkTotalHomR
  ; ProductDisplayed
  ; forgetDecorated
  ; forgetProductLeft
  ; forgetProductRight
  ; base
  ; disp
  ; dispHom
  ; mapDecorated
  ) renaming (baseHom to baseHomᴰ)

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortSigStrictification as PortSigStrictification
open PortSig using
  ( PortSig
  ; PortEntry
  ; sig
  ; TagTy
  ; LabelOf
  )

-- --------------------------------------------------------------------------
-- Universe-polymorphic list (Setω) for port entries.

infixr 5 _∷_
data Listω (A : Setω) : Setω where
  []  : Listω A
  _∷_ : A → Listω A → Listω A

-- Setω-level unit (needed because universes are not cumulative).
record ⊤ω : Setω where
  constructor ttω

-- Setω-level propositional equality (needed because `Member` lives in `Setω`).
infix 4 _≡ω_
data _≡ω_ {A : Setω} (x : A) : A → Setω where
  reflω : x ≡ω x

congω
  : ∀ {A B : Setω}
  → (f : A → B)
  → ∀ {x y}
  → x ≡ω y
  → f x ≡ω f y
congω _ reflω = reflω

⊥-elimω : ∀ {ℓ : Level} {A : Setω} → ⊥ {ℓ} → A
⊥-elimω ()

-- --------------------------------------------------------------------------
-- Port stacks and folding to a displayed structure.

infixr 5 _∷⁺_
data PortStack
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Setω where
  [_] : PortEntry C → PortStack C
  _∷⁺_ : PortEntry C → PortStack C → PortStack C

prepend
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortEntry C → PortStack C → PortStack C
prepend = _∷⁺_

binaryStack
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortEntry C → PortEntry C → PortStack C
binaryStack p q = prepend p [ q ]

head
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortStack C → PortEntry C
head [ p ] = p
head (p ∷⁺ _) = p

toList
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortStack C → Listω (PortEntry C)
toList [ p ] = p ∷ []
toList (p ∷⁺ ps) = p ∷ toList ps

StackℓDObj
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortStack C → Level
StackℓDObj [ p ] = PortSig.ℓDObj (sig p)
StackℓDObj (p ∷⁺ ps) = PortSig.ℓDObj (sig p) ⊔ StackℓDObj ps

StackℓDHom
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortStack C → Level
StackℓDHom [ p ] = PortSig.ℓDHom (sig p)
StackℓDHom (p ∷⁺ ps) = PortSig.ℓDHom (sig p) ⊔ StackℓDHom ps

StackDisplayed
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (S : PortStack C)
  → DisplayedThin2Cat C (StackℓDObj S) (StackℓDHom S)
StackDisplayed [ p ] = PortSig.Displayed (sig p)
StackDisplayed (p ∷⁺ ps) = ProductDisplayed (PortSig.Displayed (sig p)) (StackDisplayed ps)

StackCat
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (S : PortStack C)
  → Thin2Cat
      (ℓObj ⊔ StackℓDObj S)
      (ℓHomCon ⊔ StackℓDHom S)
      ℓHomRel
StackCat {C = C} S = DecoratedThin2Cat (StackDisplayed {C = C} S)

forgetStack
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (S : PortStack C)
  → Thin2Functor (StackCat {C = C} S) C
forgetStack S = forgetDecorated (StackDisplayed S)

-- Base projections for stacked ports.
--
-- These are just the `DecoratedThin2Cat` projections specialised to a stack,
-- but exposing them here avoids repeated `{D = StackDisplayed …}` boilerplate
-- in downstream ports/apps.

baseObj
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {S : PortStack C}
  → Thin2Cat.Obj (StackCat {C = C} S)
  → Thin2Cat.Obj C
baseObj {C = C} {S = S} = base {D = StackDisplayed {C = C} S}

baseHom
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {S : PortStack C}
    {X Y : Thin2Cat.Obj (StackCat {C = C} S)}
  → Con (Thin2Cat.Hom (StackCat {C = C} S) X Y)
  → Con (Thin2Cat.Hom C (baseObj {C = C} {S = S} X) (baseObj {C = C} {S = S} Y))
baseHom {C = C} {S = S} = baseHomᴰ {C = C} {D = StackDisplayed {C = C} S}

-- Naming note:
-- `baseHom` is also used for Σ-totalisations (`DisplayedThin2Cat.Totalisation`),
-- so curated API surfaces may prefer to re-export `PortStack.baseObj/baseHom`
-- under stack-specific names via `renaming`.

-- --------------------------------------------------------------------------
-- Leftmost selection on raw entry lists.
--
-- This is the small generic core behind the raw first-order-name/dependent-
-- payload split: choose a key extractor, then resolve duplicates leftmost.
--
-- - `Member` instantiates `Select` with the first-order port label.
-- - `EntryMember` instantiates `Select` with the identity key, giving exact
--   typed access to a concrete port entry.
data Select
  {A Key : Setω}
  (keyOf : A → Key)
  : Key
  → Listω A
  → Setω where
  here
    : ∀ {a : A} {rest}
    → Select keyOf (keyOf a) (a ∷ rest)
  there
    : ∀ {k : Key} {e rest}
    → Select keyOf k rest
    → Select keyOf k (e ∷ rest)

record LabelKey : Setω where
  constructor labelKey
  field
    lowerLabel : PortSig.PortLabel

Member
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortSig.PortLabel
  → Listω (PortEntry C)
  → Setω
Member {C = C} label =
  Select {A = PortEntry C} (λ p → labelKey (LabelOf p)) (labelKey label)

EntryMember
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortEntry C
  → Listω (PortEntry C)
  → Setω
EntryMember {C = C} = Select {A = PortEntry C} (λ p → p)

hereEntry
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C} {rest}
  → EntryMember p (p ∷ rest)
hereEntry = here

thereEntry
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p e : PortEntry C} {rest}
  → EntryMember p rest
  → EntryMember p (e ∷ rest)
thereEntry = there

entryMember⇒member
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {es : Listω (PortEntry C)}
  → EntryMember p es
  → Member (LabelOf p) es
entryMember⇒member here = here
entryMember⇒member (there m) = there (entryMember⇒member m)

-- Optional discipline: tag uniqueness in a stack.
--
-- If you enable instance search for membership (`module Instances` below),
-- consider carrying a `NoDupStack` proof to avoid ambiguous resolution.

mutual

  NoDupTags
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    → Listω (PortEntry C)
    → Setω
  NoDupTags [] = ⊤ω
  NoDupTags (e ∷ es) = NoDupTagsStep e es

  record NoDupTagsStep
    {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (e : PortEntry C)
    (es : Listω (PortEntry C))
    : Setω where
    inductive
    constructor mkNoDupTagsStep
    field
      notInRest : Member (LabelOf e) es → ⊥ {lzero}
      rest : NoDupTags es

NoDupStack
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortStack C
  → Setω
NoDupStack S = NoDupTags (toList S)

record MemberStack
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (p : PortEntry C)
  (S : PortStack C)
  : Setω where
  constructor mkMemberStack
  field
    member : EntryMember p (toList S)

open MemberStack public using (member)

-- Capability bundle: “this stack contains the concrete port entry `p`”.
--
-- Prefer passing `HasPort p S` across module boundaries instead of
-- raw `MemberStack` proofs. This keeps “port requirements” explicit and named,
-- while still supporting opt-in instance ergonomics (see `Instances`).
HasPort
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortEntry C
  → PortStack C
  → Setω
HasPort p S = MemberStack p S

memberStack
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → HasPort p S
  → MemberStack p S
memberStack m = m

mkHasPort
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → MemberStack p S
  → HasPort p S
mkHasPort m = m

-- Small capability constructors (ergonomics):
-- avoid exposing/hand-writing raw `MemberStack` proofs in downstream ports/apps.

hasSingleton
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
  → HasPort p [ p ]
hasSingleton {p = p} =
  mkHasPort {S = [ p ]} (mkMemberStack (hereEntry {rest = []}))

-- Singleton port packaging (boilerplate eliminator).
--
-- Many ports are defined as a single displayed layer over some base thin
-- 2-category. This record packages the canonical `PortEntry`, singleton stack,
-- and capability proof derived from a `PortSig`.
record SingletonPort
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  {ℓTag : Level}
  (Tag : Set ℓTag)
  : Setω where
  field
    {label} : PortSig.PortLabel
    portSig : PortSig C label Tag

  entry : PortEntry C
  entry = PortSig.mkEntry portSig

  stack : PortStack C
  stack = [ entry ]

  port : HasPort entry stack
  port = hasSingleton

singletonPort
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {label : PortSig.PortLabel}
    {ℓTag : Level} {Tag : Set ℓTag}
  → PortSig C label Tag
  → SingletonPort C Tag
singletonPort {label = label} sig =
  record
    { portSig = sig }

hasHead
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C} {ps : PortStack C}
  → HasPort p (p ∷⁺ ps)
hasHead {p = p} {ps = ps} =
  mkHasPort {S = p ∷⁺ ps} (mkMemberStack (hereEntry {rest = toList ps}))

hasThere
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {q : PortEntry C}
    {S : PortStack C}
    {p : PortEntry C}
  → HasPort q S
  → HasPort q (p ∷⁺ S)
hasThere {S = S} {p = p} h =
  mkHasPort {S = p ∷⁺ S}
    (mkMemberStack (thereEntry {rest = toList S} (member (memberStack h))))

hasTail
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {q : PortEntry C}
    {S : PortStack C}
    {p : PortEntry C}
  → HasPort q S
  → HasPort q (prepend p S)
hasTail = hasThere

hasSecond
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p q : PortEntry C}
  → HasPort q (binaryStack p q)
hasSecond {p = p} {q = q} = hasTail {S = [ q ]} {p = p} hasSingleton

sigAtList
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C} {es : Listω (PortEntry C)}
  → EntryMember p es
  → PortSig C (LabelOf p) (TagTy p)
sigAtList {p = p} _ = sig p

sigAt
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → MemberStack p S
  → PortSig C (LabelOf p) (TagTy p)
sigAt m = sigAtList (member m)

getObjPort
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → (m : MemberStack p S)
  → (X : DecoratedObj (StackDisplayed S))
  → Ob (PortSig.Displayed (sigAt m)) (base {D = StackDisplayed S} X)
getObjPort {S = [ p ]} (mkMemberStack here) X =
  disp {D = StackDisplayed [ p ]} X
getObjPort {S = q ∷⁺ ps} (mkMemberStack here) X =
  fst (disp {D = StackDisplayed (q ∷⁺ ps)} X)
getObjPort {S = q ∷⁺ ps} (mkMemberStack (there m)) X =
  getObjPort {S = ps} (mkMemberStack m)
    (mkTotalObjR
      (base {D = StackDisplayed (q ∷⁺ ps)} X)
      (snd (disp {D = StackDisplayed (q ∷⁺ ps)} X)))

getHomPort
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → (m : MemberStack p S)
  → {X Y : DecoratedObj (StackDisplayed S)}
  → (f : DecoratedHom (StackDisplayed S) X Y)
  → HomD
      (PortSig.Displayed (sigAt m))
      (baseHomᴰ {D = StackDisplayed S} f)
      (getObjPort m X)
      (getObjPort m Y)
getHomPort {S = [ p ]} (mkMemberStack here) f =
  dispHom {D = StackDisplayed [ p ]} f
getHomPort {S = q ∷⁺ ps} (mkMemberStack here) f =
  fst (dispHom {D = StackDisplayed (q ∷⁺ ps)} f)
getHomPort {S = q ∷⁺ ps} (mkMemberStack (there m)) {X = X} {Y = Y} f =
  getHomPort {S = ps} (mkMemberStack m)
    {X =
      mkTotalObjR
        (base {D = StackDisplayed (q ∷⁺ ps)} X)
        (snd (disp {D = StackDisplayed (q ∷⁺ ps)} X))}
    {Y =
      mkTotalObjR
        (base {D = StackDisplayed (q ∷⁺ ps)} Y)
        (snd (disp {D = StackDisplayed (q ∷⁺ ps)} Y))}
    (mkTotalHomR
      (baseHomᴰ {D = StackDisplayed (q ∷⁺ ps)} f)
      (snd (dispHom {D = StackDisplayed (q ∷⁺ ps)} f)))

getObj
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → (h : HasPort p S)
  → (X : DecoratedObj (StackDisplayed S))
  → Ob (PortSig.Displayed (sigAt (memberStack h))) (base {D = StackDisplayed S} X)
getObj h = getObjPort (memberStack h)

getHom
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → (h : HasPort p S)
  → {X Y : DecoratedObj (StackDisplayed S)}
  → (f : DecoratedHom (StackDisplayed S) X Y)
  → HomD
      (PortSig.Displayed (sigAt (memberStack h)))
      (baseHomᴰ {D = StackDisplayed S} f)
      (getObjPort (memberStack h) X)
      (getObjPort (memberStack h) Y)
getHom h = getHomPort (memberStack h)

forgetToPort
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → (m : MemberStack p S)
  → Thin2Functor (StackCat S) (DecoratedThin2Cat (PortSig.Displayed (sigAt m)))
forgetToPort {S = [ p ]} (mkMemberStack here) =
  idThin2Functor (DecoratedThin2Cat (StackDisplayed [ p ]))
forgetToPort {S = q ∷⁺ ps} (mkMemberStack here) =
  let
    D₁ = PortSig.Displayed (sig q)
    D₂ = StackDisplayed ps
  in
  forgetProductLeft D₁ D₂
forgetToPort {S = q ∷⁺ [ p ]} (mkMemberStack (there here)) =
  let
    D₁ = PortSig.Displayed (sig q)
    D₂ = StackDisplayed [ p ]
  in
  forgetProductRight D₁ D₂
forgetToPort {S = q ∷⁺ (r ∷⁺ rs)} (mkMemberStack (there m)) =
  let
    D₁ = PortSig.Displayed (sig q)
    D₂ = StackDisplayed (r ∷⁺ rs)
  in
  forgetToPort {S = r ∷⁺ rs} (mkMemberStack m) ∘F forgetProductRight D₁ D₂

forgetPort
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → (h : HasPort p S)
  → Thin2Functor (StackCat S) (DecoratedThin2Cat (PortSig.Displayed (sigAt (memberStack h))))
forgetPort h = forgetToPort (memberStack h)

-- --------------------------------------------------------------------------
-- Substack masks: forget to an arbitrary substack of ports.

data Substack
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  : PortStack C → PortStack C → Setω where
  last : ∀ {p} → Substack [ p ] [ p ]
  keep : ∀ {p Y X} → Substack Y X → Substack (p ∷⁺ Y) (p ∷⁺ X)
  drop : ∀ {p Y X} → Substack Y X → Substack Y (p ∷⁺ X)

private
  objMapSubstack
    : ∀ {ℓObj ℓHomCon ℓHomRel}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {Y X : PortStack C}
    → Substack Y X
    → ∀ {A}
    → Ob (StackDisplayed X) A
    → Ob (StackDisplayed Y) A
  objMapSubstack last x = x
  objMapSubstack (keep p) (x₁ , x₂) = x₁ , objMapSubstack p x₂
  objMapSubstack (drop p) (_ , x₂) = objMapSubstack p x₂

  homMapSubstack
    : ∀ {ℓObj ℓHomCon ℓHomRel}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {Y X : PortStack C}
    → (p : Substack Y X)
    → ∀ {A B} {f : Con (Thin2Cat.Hom C A B)}
      {x : Ob (StackDisplayed X) A}
      {y : Ob (StackDisplayed X) B}
    → HomD (StackDisplayed X) f x y
    → HomD (StackDisplayed Y) f (objMapSubstack p x) (objMapSubstack p y)
  homMapSubstack last h = h
  homMapSubstack (keep p) (h₁ , h₂) = h₁ , homMapSubstack p h₂
  homMapSubstack (drop p) (_ , h₂) = homMapSubstack p h₂

forgetSubstack
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Y X : PortStack C}
  → (p : Substack Y X)
  → Thin2Functor (StackCat X) (StackCat Y)
forgetSubstack {Y = Y} {X = X} p =
  mapDecorated
    (StackDisplayed X)
    (StackDisplayed Y)
    (objMapSubstack {Y = Y} {X = X} p)
    (homMapSubstack {Y = Y} {X = X} p)

-- --------------------------------------------------------------------------
-- Optional instance ergonomics (explicit opt-in).

module Instances where

  instance
    memberHere
      : ∀ {ℓObj ℓHomCon ℓHomRel}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {label : PortSig.PortLabel}
        {ℓTag : Level} {Tag : Set ℓTag} {sig : PortSig C label Tag} {rest}
      → Member label (PortSig.mkPortEntry label ℓTag Tag sig ∷ rest)
    memberHere = here

  instance
    memberThere
      : ∀ {ℓObj ℓHomCon ℓHomRel}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {label : PortSig.PortLabel} {rest}
        {e : PortEntry C}
      → {{Member label rest}}
      → Member label (e ∷ rest)
    memberThere {{m}} = there m

  instance
    entryMemberHere
      : ∀ {ℓObj ℓHomCon ℓHomRel}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {p : PortEntry C} {rest}
      → EntryMember p (p ∷ rest)
    entryMemberHere = hereEntry

  instance
    entryMemberThere
      : ∀ {ℓObj ℓHomCon ℓHomRel}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {p e : PortEntry C} {rest}
      → {{EntryMember p rest}}
      → EntryMember p (e ∷ rest)
    entryMemberThere {{m}} = thereEntry m

  instance
    memberStackFromEntryMember
      : ∀ {ℓObj ℓHomCon ℓHomRel}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {p : PortEntry C} {S : PortStack C}
      → {{EntryMember p (toList S)}}
      → MemberStack p S
    memberStackFromEntryMember {{m}} = mkMemberStack m

  instance
    hasPortFromMember
      : ∀ {ℓObj ℓHomCon ℓHomRel}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {p : PortEntry C} {S : PortStack C}
      → {{MemberStack p S}}
      → HasPort p S
    hasPortFromMember {{m}} = m

  port
    : ∀ {ℓObj ℓHomCon ℓHomRel}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {p : PortEntry C} {S : PortStack C}
    → {{hp : HasPort p S}}
    → (X : DecoratedObj (StackDisplayed S))
    → Ob (PortSig.Displayed (sigAt (memberStack hp))) (base {D = StackDisplayed S} X)
  port {{hp}} = getObjPort (memberStack hp)

pullbackPortStack
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → StrictThin2Functor C₁ C₂
  → PortStack C₂
  → PortStack C₁
pullbackPortStack SF [ p ] =
  [ PortSigStrictification.pullbackPortEntry SF p ]
pullbackPortStack SF (p ∷⁺ ps) =
  PortSigStrictification.pullbackPortEntry SF p ∷⁺ pullbackPortStack SF ps
