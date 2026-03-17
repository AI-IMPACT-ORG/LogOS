{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.Template.Singleton2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Port authoring template (singleton case).
--
-- Many `*2Cat` modules define a single displayed layer over some base thin 2-category `C`
-- (often `LOG ...`) and then take the Σ-totalisation (`DecoratedThin2Cat`) to obtain a
-- new thin 2-category with inherited refinements.
--
-- This module factors out the mechanical packaging:
-- - build the canonical `SingletonPort` from a `PortSig`,
-- - derive the singleton `PortStack`, its total category, and the forgetful functor,
-- - provide the definitional-equality “discipline hook” as a `refl` proof.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedThin2Cat
  ; forgetDecorated
  )
import LogOS.LT.DisplayedThin2Cat.SuccessorStage as Successor

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack

mkPortSig
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {ℓTag : Level}
    {Tag : Set ℓTag}
    {ℓDObj ℓDHom : Level}
  → (label : PortSig.PortLabel)
  → DisplayedThin2Cat C ℓDObj ℓDHom
  → PortSig.PortSig C label Tag
mkPortSig {ℓDObj = ℓDObj} {ℓDHom = ℓDHom} label Displayed =
  record
    { ℓDObj = ℓDObj
    ; ℓDHom = ℓDHom
    ; Displayed = Displayed
    }

record Singleton2Cat
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (label : PortSig.PortLabel)
  {ℓTag : Level}
  (Tag : Set ℓTag)
  : Setω where
  constructor mkSingleton2Cat
  field
    portSig : PortSig.PortSig C label Tag

  singleton : PortStack.SingletonPort C Tag
  singleton = PortStack.singletonPort portSig

  stack : PortStack.PortStack C
  stack = PortStack.SingletonPort.stack singleton

  port : PortStack.HasPort (PortStack.SingletonPort.entry singleton) stack
  port = PortStack.SingletonPort.port singleton

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

  -- Discipline hook: if you define a port as `StackDisplayed (SingletonPort.stack …)`,
  -- this proof should remain definitionally `refl`.
  displayed≡
    : PortStack.StackDisplayed stack
      ≡ PortSig.Displayed portSig
  displayed≡ = refl

  withPort≡
    : WithPort ≡ DecoratedThin2Cat Displayed
  withPort≡ = refl

  forget≡
    : forget ≡ forgetDecorated Displayed
  forget≡ = refl

open Singleton2Cat public using
  ( singleton
  ; stack
  ; port
  ; successor
  ; Displayed
  ; WithPort
  ; Next
  ; forget
  )

module SingletonExports
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {label : PortSig.PortLabel}
  {ℓTag : Level}
  {Tag : Set ℓTag}
  (sig : PortSig.PortSig C label Tag)
  where

  port2Cat : Singleton2Cat C label Tag
  port2Cat = mkSingleton2Cat sig

  open Singleton2Cat port2Cat public using
    ( singleton
    ; stack
    ; port
    ; successor
    ; Displayed
    ; WithPort
    ; Next
    ; forget
    )

module SingletonLayer
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (label : PortSig.PortLabel)
  {ℓTag : Level}
  {Tag : Set ℓTag}
  {ℓDObj ℓDHom : Level}
  (Displayed : DisplayedThin2Cat C ℓDObj ℓDHom)
  where

  portSig : PortSig.PortSig C label Tag
  portSig = mkPortSig {Tag = Tag} label Displayed

  open SingletonExports portSig public
