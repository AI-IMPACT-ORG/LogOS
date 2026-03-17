{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack.Unique where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Uniqueness-safe port access.
--
-- The core `PortStack` machinery allows duplicate tags and resolves them
-- leftmost. This module adds an explicit opt-in layer for public stacks that
-- are intended to be unambiguous.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Ports.PortSig using (PortEntry; LabelOf)
open import LogOS.LT.Ports.PortStack.Raw using
  ( PortStack
  ; [_]
  ; _∷⁺_
  ; ⊤ω
  ; ttω
  ; ⊥-elimω
  ; Listω
  ; []
  ; Member
  ; here
  ; there
  ; NoDupTags
  ; NoDupTagsStep
  ; mkNoDupTagsStep
  ; NoDupStack
  ; MemberStack
  ; HasPort
  ; memberStack
  )

record UniquePort
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (p : PortEntry C)
  (S : PortStack C)
  : Setω where
  constructor mkUniquePort
  field
    hasPort : HasPort p S
    noDup : NoDupStack S

open UniquePort public using (hasPort; noDup)

record UniquePortStack
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Setω where
  constructor mkUniquePortStack
  field
    rawStack : PortStack C
    stackNoDup : NoDupStack rawStack

open UniquePortStack public using (rawStack; stackNoDup)

uniqueHasPort
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → UniquePort p S
  → HasPort p S
uniqueHasPort = hasPort

uniqueMember
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {S : PortStack C}
  → UniquePort p S
  → MemberStack p S
uniqueMember up = memberStack (hasPort up)

noDupNil
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → NoDupTags ([] {A = PortEntry C})
noDupNil = ttω

noDupSingleton
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
  → NoDupStack [ p ]
noDupSingleton {C = C} =
  mkNoDupTagsStep
    (λ ())
    (noDupNil {C = C})

singletonUniqueStack
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
  → UniquePortStack C
singletonUniqueStack {p = p} =
  mkUniquePortStack [ p ] noDupSingleton

noDupCons
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {p : PortEntry C}
    {ps : PortStack C}
  → (Member (LabelOf p) (LogOS.LT.Ports.PortStack.Raw.toList ps) → ⊥ {lzero})
  → NoDupStack ps
  → NoDupStack (p ∷⁺ ps)
noDupCons notInRest noDupPs =
  mkNoDupTagsStep
    (λ m → notInRest m)
    noDupPs

module UniqueInstances where

  instance
    uniquePortFromNoDup
      : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {p : PortEntry C}
        {S : PortStack C}
      → {{hp : HasPort p S}}
      → {{nd : NoDupStack S}}
      → UniquePort p S
    uniquePortFromNoDup {{hp}} {{nd}} = mkUniquePort hp nd

  instance
    hasPortFromUnique
      : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
        {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
        {p : PortEntry C}
        {S : PortStack C}
      → {{up : UniquePort p S}}
      → HasPort p S
    hasPortFromUnique {{up}} = hasPort up
