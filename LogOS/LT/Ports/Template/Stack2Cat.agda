{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.Template.Stack2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Port authoring template (stack case).
--
-- Many architecture-first composite port modules define a `PortStack` (non-empty, right-associated
-- `ProductDisplayed`) and then take the Σ-totalisation (`DecoratedThin2Cat`) to obtain a
-- new thin 2-category with inherited refinements.
--
-- This module packages the mechanical parts:
-- - a port stack over a base thin 2-category,
-- - its folded displayed structure,
-- - the total category and forgetful functor,
-- - base projections (`baseObj` / `baseHom`) for convenience.

open import LogOS.Prelude

open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedThin2Cat
  ; forgetDecorated
  ; ProductDisplayed
  ; forgetProductLeft
  ; forgetProductRight
  )
import LogOS.LT.DisplayedThin2Cat.SuccessorStage as Successor

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack

record Stack2Cat
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Setω where
  constructor mkStack2Cat
  field
    stack : PortStack.PortStack C

  successor : Successor.SuccessorStage C
  successor = Successor.mkSuccessorStage (PortStack.StackDisplayed stack)

  Displayed : DisplayedThin2Cat C _ _
  Displayed = Successor.Displayed successor

  WithPort : Thin2Cat _ _ _
  WithPort = Successor.Next successor

  Next : Thin2Cat _ _ _
  Next = WithPort

  forget : Thin2Functor WithPort C
  forget = Successor.forget successor

  baseObj : Thin2Cat.Obj WithPort → Thin2Cat.Obj C
  baseObj = Successor.baseObj successor

  baseHom
    : ∀ {X Y : Thin2Cat.Obj WithPort}
    → Con (Thin2Cat.Hom WithPort X Y)
    → Con (Thin2Cat.Hom C (baseObj X) (baseObj Y))
  baseHom = Successor.baseHom successor

  displayed≡
    : Displayed ≡ PortStack.StackDisplayed stack
  displayed≡ = refl

  withPort≡
    : WithPort ≡ DecoratedThin2Cat Displayed
  withPort≡ = refl

  forget≡
    : forget ≡ forgetDecorated Displayed
  forget≡ = refl

open Stack2Cat public using
  ( stack
  ; Displayed
  ; successor
  ; WithPort
  ; Next
  ; forget
  ; baseObj
  ; baseHom
  )

mkPrependedStack2Cat
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortSig.PortEntry C
  → PortStack.PortStack C
  → Stack2Cat C
mkPrependedStack2Cat p ps =
  mkStack2Cat (PortStack.prepend p ps)

mkBinaryStack2Cat
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → PortSig.PortEntry C
  → PortSig.PortEntry C
  → Stack2Cat C
mkBinaryStack2Cat p q =
  mkStack2Cat (PortStack.binaryStack p q)

module StackExports
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (stack2Cat : Stack2Cat C)
  where

  open Stack2Cat stack2Cat public using
    ( stack
    ; Displayed
    ; successor
    ; WithPort
    ; Next
    ; forget
    ; baseObj
    ; baseHom
    )

module StackLayer
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (stack : PortStack.PortStack C)
  where

  stack2Cat : Stack2Cat C
  stack2Cat = mkStack2Cat stack

  open StackExports stack2Cat public

module PrependedStackExports
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (p : PortSig.PortEntry C)
  (ps : PortStack.PortStack C)
  where

  stack2Cat : Stack2Cat C
  stack2Cat = mkPrependedStack2Cat p ps

  open StackExports stack2Cat public

module BinaryStackExports
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (p : PortSig.PortEntry C)
  (q : PortSig.PortEntry C)
  where

  stack2Cat : Stack2Cat C
  stack2Cat = mkBinaryStack2Cat p q

  open StackExports stack2Cat public

module SingletonPortStackExports
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {ℓTag : Level}
  {Tag : Set ℓTag}
  (singleton : PortStack.SingletonPort C Tag)
  where

  stack2Cat : Stack2Cat C
  stack2Cat = mkStack2Cat (PortStack.SingletonPort.stack singleton)

  open StackExports stack2Cat public

  port : PortStack.HasPort (PortStack.SingletonPort.entry singleton) (Stack2Cat.stack stack2Cat)
  port = PortStack.SingletonPort.port singleton

module BinaryEntryStackExports
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (left : PortSig.PortEntry C)
  (right : PortSig.PortEntry C)
  where

  stack2Cat : Stack2Cat C
  stack2Cat = mkBinaryStack2Cat left right

  open StackExports stack2Cat public

  headPort : PortStack.HasPort left (Stack2Cat.stack stack2Cat)
  headPort = PortStack.hasHead {ps = PortStack.[ right ]}

  secondPort : PortStack.HasPort right (Stack2Cat.stack stack2Cat)
  secondPort = PortStack.hasSecond {p = left} {q = right}

  Displayed-product
    : Stack2Cat.Displayed stack2Cat
      ≡
      ProductDisplayed
        (PortSig.Displayed (PortSig.sig left))
        (PortSig.Displayed (PortSig.sig right))
  Displayed-product = refl

  forgetHead-product
    : PortStack.forgetPort headPort
      ≡
      forgetProductLeft
        (PortSig.Displayed (PortSig.sig left))
        (PortSig.Displayed (PortSig.sig right))
  forgetHead-product = refl

  forgetSecond-product
    : PortStack.forgetPort secondPort
      ≡
      forgetProductRight
        (PortSig.Displayed (PortSig.sig left))
        (PortSig.Displayed (PortSig.sig right))
  forgetSecond-product = refl

module BinarySingletonStackExports
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {ℓTag₁ : Level}
  {Tag₁ : Set ℓTag₁}
  {ℓTag₂ : Level}
  {Tag₂ : Set ℓTag₂}
  (left : PortStack.SingletonPort C Tag₁)
  (right : PortStack.SingletonPort C Tag₂)
  where

  open BinaryEntryStackExports
    (PortStack.SingletonPort.entry left)
    (PortStack.SingletonPort.entry right)
    public
    renaming
      ( headPort to leftPort
      ; secondPort to rightPort
      ; forgetHead-product to forgetLeft-product
      ; forgetSecond-product to forgetRight-product
      )
