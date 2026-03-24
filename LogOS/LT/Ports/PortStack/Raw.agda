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

-- Setω-level propositional equality (needed because raw bookkeeping lives in `Setω`).
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
-- This is the small generic core behind exact-entry stack access: choose a key
-- extractor, then resolve duplicates leftmost.
--
-- Both `Member` and `EntryMember` use the concrete port entry itself as the
-- lookup key.
data Select
  {A Key : Setω}
  (keyOf : A → Key)
  : Key
  → Listω A
  → Setω where
  selectHere
    : ∀ {a : A} {rest}
    → Select keyOf (keyOf a) (a ∷ rest)
  selectThere
    : ∀ {k : Key} {e rest}
    → Select keyOf k rest
    → Select keyOf k (e ∷ rest)

Member
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortEntry C
  → Listω (PortEntry C)
  → Setω
Member {C = C} = Select {A = PortEntry C} (λ p → p)

EntryMember
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortEntry C
  → Listω (PortEntry C)
  → Setω
EntryMember = Member

here
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C} {rest}
  → Member p (p ∷ rest)
here = selectHere

there
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p e : PortEntry C} {rest}
  → Member p rest
  → Member p (e ∷ rest)
there = selectThere

hereEntry
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C} {rest}
  → EntryMember p (p ∷ rest)
hereEntry = selectHere

thereEntry
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p e : PortEntry C} {rest}
  → EntryMember p rest
  → EntryMember p (e ∷ rest)
thereEntry = selectThere

entryMember⇒member
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {es : Listω (PortEntry C)}
  → EntryMember p es
  → Member p es
entryMember⇒member m = m

-- Public uniqueness certification for structural stacks.
--
-- Exact-entry capabilities already determine how clients access a stack. The
-- `NoDupStack` witness is therefore a public certification token attached to
-- stacks that are exported in the uniqueness-first lane.
data NoDupStack
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortStack C
  → Setω where
  noDupSingletonR
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {p : PortEntry C}
    → NoDupStack [ p ]
  noDupStepR
    : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
      {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
      {p : PortEntry C}
      {ps : PortStack C}
    → NoDupStack ps
    → NoDupStack (p ∷⁺ ps)

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
    portSig : PortSig C Tag

  entry : PortEntry C
  entry = PortSig.mkEntry portSig

  stack : PortStack C
  stack = [ entry ]

  port : HasPort entry stack
  port = hasSingleton

singletonPort
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {ℓTag : Level} {Tag : Set ℓTag}
  → PortSig C Tag
  → SingletonPort C Tag
singletonPort sig =
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
  → PortSig C (TagTy p)
sigAtList {p = p} _ = sig p

sigAt
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → MemberStack p S
  → PortSig C (TagTy p)
sigAt m = sigAtList (member m)

getObjPort
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → (m : MemberStack p S)
  → (X : DecoratedObj (StackDisplayed S))
  → Ob (PortSig.Displayed (sigAt m)) (base {D = StackDisplayed S} X)
getObjPort {S = [ p ]} (mkMemberStack selectHere) X =
  disp {D = StackDisplayed [ p ]} X
getObjPort {S = q ∷⁺ ps} (mkMemberStack selectHere) X =
  fst (disp {D = StackDisplayed (q ∷⁺ ps)} X)
getObjPort {S = q ∷⁺ ps} (mkMemberStack (selectThere m)) X =
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
getHomPort {S = [ p ]} (mkMemberStack selectHere) f =
  dispHom {D = StackDisplayed [ p ]} f
getHomPort {S = q ∷⁺ ps} (mkMemberStack selectHere) f =
  fst (dispHom {D = StackDisplayed (q ∷⁺ ps)} f)
getHomPort {S = q ∷⁺ ps} (mkMemberStack (selectThere m)) {X = X} {Y = Y} f =
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
forgetToPort {S = [ p ]} (mkMemberStack selectHere) =
  idThin2Functor (DecoratedThin2Cat (StackDisplayed [ p ]))
forgetToPort {S = q ∷⁺ ps} (mkMemberStack selectHere) =
  let
    D₁ = PortSig.Displayed (sig q)
    D₂ = StackDisplayed ps
  in
  forgetProductLeft D₁ D₂
forgetToPort {S = q ∷⁺ [ p ]} (mkMemberStack (selectThere selectHere)) =
  let
    D₁ = PortSig.Displayed (sig q)
    D₂ = StackDisplayed [ p ]
  in
  forgetProductRight D₁ D₂
forgetToPort {S = q ∷⁺ (r ∷⁺ rs)} (mkMemberStack (selectThere m)) =
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
        {p : PortEntry C}
        {rest}
      → Member p (p ∷ rest)
    memberHere = selectHere

  instance
    memberThere
      : ∀ {ℓObj ℓHomCon ℓHomRel}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {p : PortEntry C} {rest}
        {e : PortEntry C}
      → {{Member p rest}}
      → Member p (e ∷ rest)
    memberThere {{m}} = selectThere m

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
