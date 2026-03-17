{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack.ClassicalLimit where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- LOG-specialised helpers: add explicit classical-limit / strict-decode law ports
-- to an arbitrary port stack, and strictify uniformly.
-- (“Classical limit” here means extensional/posetal collapse, not classical logic/LEM.)

open import LogOS.Prelude
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using (Ob; HomD; DecoratedObj; DecoratedHom; base; baseHom)
open import LogOS.LT.Kernel using (bnd)
open import LogOS.LT.ConPreorder.Antisymmetry using (Antisymmetry)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.LOG.ClassicalLimit2Cat as ClassicalLimit2Cat
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode2Cat

withClassicalLimit
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})
  → PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})
withClassicalLimit {ℓ} {ℓRel} {ℓCode} S =
  PortStack.SingletonPort.entry (ClassicalLimit2Cat.singleton {ℓ} {ℓRel} {ℓCode})
    PortStack.∷⁺
    S

withStrictDecode
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})
  → PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})
withStrictDecode {ℓ} {ℓRel} {ℓCode} S =
  PortStack.SingletonPort.entry (StrictDecode2Cat.singleton {ℓ} {ℓRel} {ℓCode})
    PortStack.∷⁺
    S

strictifyStack
  : ∀ {ℓ ℓRel ℓCode : Level}
  → (S : PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode}))
  → Thin2Functor
      (PortStack.StackCat (withClassicalLimit {ℓ} {ℓRel} {ℓCode} S))
      (PortStack.StackCat (withStrictDecode {ℓ} {ℓRel} {ℓCode} S))
strictifyStack {ℓ} {ℓRel} {ℓCode} S =
  ClassicalLimit2Cat.strictifyDisplayed {ℓ} {ℓRel} {ℓCode} {D = PortStack.StackDisplayed S}

-- --------------------------------------------------------------------------
-- Capability bundles (ergonomics): name the common law ports explicitly.
--
-- These are intentionally tiny wrappers around `PortStack.HasPort`, so
-- downstream code can request a capability (“has strict decode”) without
-- mentioning the tag type at every call site (and without passing raw
-- membership proofs around).

record HasClassicalLimit
  {ℓ ℓRel ℓCode : Level}
  (S : PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode}))
  : Setω where
  field
    hasPort : PortStack.HasPort (PortStack.SingletonPort.entry (ClassicalLimit2Cat.singleton {ℓ} {ℓRel} {ℓCode})) S

open HasClassicalLimit public

record HasStrictDecode
  {ℓ ℓRel ℓCode : Level}
  (S : PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode}))
  : Setω where
  field
    hasPort : PortStack.HasPort (PortStack.SingletonPort.entry (StrictDecode2Cat.singleton {ℓ} {ℓRel} {ℓCode})) S

open HasStrictDecode public

classicalLimitOf
  : ∀ {ℓ ℓRel ℓCode : Level}
    {S : PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})}
  → (h : HasClassicalLimit S)
  → (X : DecoratedObj (PortStack.StackDisplayed S))
  → Ob (PortSig.Displayed (PortStack.sigAt (PortStack.memberStack (hasPort h))))
      (PortStack.baseObj {S = S} X)
classicalLimitOf {S = S} h =
  PortStack.getObj (hasPort h)

strictDecodeLawOf
  : ∀ {ℓ ℓRel ℓCode : Level}
    {S : PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})}
  → (h : HasStrictDecode S)
  → ∀ {X Y : DecoratedObj (PortStack.StackDisplayed S)}
  → (f : DecoratedHom (PortStack.StackDisplayed S) X Y)
  → HomD
      (PortSig.Displayed (PortStack.sigAt (PortStack.memberStack (hasPort h))))
      (PortStack.baseHom {S = S} f)
      (PortStack.getObj (hasPort h) X)
      (PortStack.getObj (hasPort h) Y)
strictDecodeLawOf {S = S} h =
  PortStack.getHom (hasPort h)

-- Canonical membership and projections for stacks built via this module.

classicalLimitOfStack
  : ∀ {ℓ ℓRel ℓCode : Level}
    {S : PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})}
  → (X : DecoratedObj (PortStack.StackDisplayed (withClassicalLimit {ℓ} {ℓRel} {ℓCode} S)))
  → Antisymmetry (bnd (PortStack.baseObj {S = withClassicalLimit {ℓ} {ℓRel} {ℓCode} S} X))
classicalLimitOfStack {ℓ} {ℓRel} {ℓCode} {S = S} =
  PortStack.getObj
    {C = LOG {ℓ} {ℓRel} {ℓCode}}
    {S = withClassicalLimit {ℓ} {ℓRel} {ℓCode} S}
    PortStack.hasHead

strictDecodeLawOfStack
  : ∀ {ℓ ℓRel ℓCode : Level}
    {S : PortStack.PortStack (LOG {ℓ} {ℓRel} {ℓCode})}
  → ∀ {X Y : DecoratedObj (PortStack.StackDisplayed (withStrictDecode {ℓ} {ℓRel} {ℓCode} S))}
  → (f : DecoratedHom (PortStack.StackDisplayed (withStrictDecode {ℓ} {ℓRel} {ℓCode} S)) X Y)
  → StrictDecode2Cat.StrictDecodeLaw
      (PortStack.baseHom
        {C = LOG {ℓ} {ℓRel} {ℓCode}}
        {S = withStrictDecode {ℓ} {ℓRel} {ℓCode} S}
        {X = X}
        {Y = Y}
        f)
strictDecodeLawOfStack {ℓ} {ℓRel} {ℓCode} {S = S} {X = X} {Y = Y} f =
  PortStack.getHom
    {C = LOG {ℓ} {ℓRel} {ℓCode}}
    {S = withStrictDecode {ℓ} {ℓRel} {ℓCode} S}
    PortStack.hasHead
    {X = X} {Y = Y}
    f
