{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.ProgDisplayed where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; _⊑_
  ; _≈_
  ; ≈-refl
  )
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Kernel using (Kernel; CodePreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; _∘F_)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)

import LogOS.LT.Ports.Template.LawSingleton2Cat as LawTemplate
import LogOS.LT.Ports.Template.Singleton2Cat as Template

import LogOS.Apps.TuringCategory.PartialMaps as PM
open import LogOS.Apps.TuringCategory.Lift using (LiftCP)

open import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.Types using
  ( Prog
  ; _++_
  ; _∷_
  ; []
  ; semAtom
  ; semProg
  )
open import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.ParOnKernels using
  ( ParOnKernels
  ; forgetParOnKernels
  )

-- --------------------------------------------------------------------------
-- Σ-totalisation: decorate partial maps with an observation program implementation.

record ProgOb : Set where
  constructor ttProg

-- Implementation: a program whose `Par` semantics matches the base partial map (up to `≈`).
ProgImplementation
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B : Kernel ℓ ℓRel ℓCode}
  → Con (Thin2Cat.Hom (ParOnKernels {ℓ} {ℓRel} {ℓCode}) A B)
  → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
ProgImplementation {A = A} {B = B} f =
  Σ
    (Prog A B)
    (λ p →
      _≈_
        (PM.PartialMapPreorder (CodePreorder A) (CodePreorder B))
        (semProg p)
        f)

idProgImplementation
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A : Kernel ℓ ℓRel ℓCode}
  → ProgImplementation {ℓ} {ℓRel} {ℓCode} {A = A} {B = A}
      (Thin2Cat.id (ParOnKernels {ℓ} {ℓRel} {ℓCode}) {A})
idProgImplementation {A = A} =
  record
    { proj₁ = []
    ; proj₂ = ≈-refl (PM.PartialMapPreorder (CodePreorder A) (CodePreorder A)) PM.idp
    }

-- Helper: composition respects mutual refinement in both arguments.
comp-≈
  : ∀ {ℓCon ℓRel : Level}
    {A B C : ConPreorder ℓCon ℓRel}
    {f f' : PM.PartialMap B C}
    {g g' : PM.PartialMap A B}
  → _≈_ (PM.PartialMapPreorder B C) f f'
  → _≈_ (PM.PartialMapPreorder A B) g g'
  → _≈_ (PM.PartialMapPreorder A C) (f PM.∘p g) (f' PM.∘p g')
comp-≈
  {ℓCon} {ℓRel}
  {A = A} {B = B} {C = C}
  {f = f} {f' = f'} {g = g} {g' = g'}
  (record { fst = ff' ; snd = f'f })
  (record { fst = gg' ; snd = g'g }) =
  let
    module P = Thin2Cat (PM.Par {ℓCon} {ℓRel})
    module R = ≤-Reasoning (PM.PartialMapPreorder A C)
    open R using (_⊑⟨_⟩_)
  in
  let
    left =
      _⊑⟨_⟩_ (f P.∘ g)
        {b = f' P.∘ g}
        {c = f' P.∘ g'}
        (P.comp-mono-l {A = A} {B = B} {C = C} {f = f} {f' = f'} {g = g} ff')
        (P.comp-mono-r {A = A} {B = B} {C = C} {f = f'} {g = g} {g' = g'} gg')

    right =
      _⊑⟨_⟩_ (f' P.∘ g')
        {b = f P.∘ g'}
        {c = f P.∘ g}
        (P.comp-mono-l {A = A} {B = B} {C = C} {f = f'} {f' = f} {g = g'} f'f)
        (P.comp-mono-r {A = A} {B = B} {C = C} {f = f} {g = g'} {g' = g} g'g)
  in
  record { fst = left ; snd = right }

-- Semantics of append: `semProg (p ++ q) ≈ semProg q ∘ semProg p`.
semProg-append
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B C : Kernel ℓ ℓRel ℓCode}
    (p : Prog A B)
    (q : Prog B C)
  → _≈_
      (PM.PartialMapPreorder (CodePreorder A) (CodePreorder C))
      (semProg (p ++ q))
      (semProg q PM.∘p semProg p)
semProg-append {B = B} {C = C} [] q =
  -- semProg ([] ++ q) = semProg q, and `f ∘ idp ≈ f`.
  let record { fst = f∘id≤f ; snd = f≤f∘id } =
        PM.Par-id-right {A = CodePreorder B} {B = CodePreorder C} (semProg q)
  in
  record { fst = f≤f∘id ; snd = f∘id≤f }
semProg-append {ℓRel = ℓRel} {ℓCode = ℓCode} {A = A} {C = C} (_∷_ {C = A₀} a p) q =
  let
    CP = PM.PartialMapPreorder (CodePreorder A) (CodePreorder C)
    module R = ≤-Reasoning CP
    open R using (_≈⟨_⟩_)
  in
  let
    step₁ : _≈_ CP
              (semProg ((a ∷ p) ++ q))
              ((semProg q PM.∘p semProg p) PM.∘p semAtom a)
    step₁ =
      comp-≈
        {ℓCon = ℓCode}
        {ℓRel = ℓRel}
        {A = CodePreorder A}
        {B = CodePreorder A₀}
        {C = CodePreorder C}
        {f = semProg (p ++ q)}
        {f' = semProg q PM.∘p semProg p}
        {g = semAtom a}
        {g' = semAtom a}
        (semProg-append p q)
        (≈-refl
          (PM.PartialMapPreorder (CodePreorder A) (CodePreorder A₀))
          (semAtom a))

    step₂ : _≈_ CP
              (((semProg q PM.∘p semProg p) PM.∘p semAtom a))
              (semProg q PM.∘p (semProg p PM.∘p semAtom a))
    step₂ = PM.Par-assoc (semProg q) (semProg p) (semAtom a)
  in
  _≈⟨_⟩_ (semProg ((a ∷ p) ++ q))
    {b = (semProg q PM.∘p semProg p) PM.∘p semAtom a}
    {c = semProg q PM.∘p (semProg p PM.∘p semAtom a)}
    step₁ step₂

compProgImplementation
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B C : Kernel ℓ ℓRel ℓCode}
    {f : Con (Thin2Cat.Hom (ParOnKernels {ℓ} {ℓRel} {ℓCode}) A B)}
    {g : Con (Thin2Cat.Hom (ParOnKernels {ℓ} {ℓRel} {ℓCode}) B C)}
  → ProgImplementation {ℓ} {ℓRel} {ℓCode} {A = A} {B = B} f
  → ProgImplementation {ℓ} {ℓRel} {ℓCode} {A = B} {B = C} g
  → ProgImplementation {ℓ} {ℓRel} {ℓCode} {A = A} {B = C}
      (g PM.∘p f)
compProgImplementation {ℓ} {ℓRel} {ℓCode} {A = A} {B = B} {C = C} {f = f} {g = g}
  (record { proj₁ = p ; proj₂ = semP≈f })
  (record { proj₁ = q ; proj₂ = semQ≈g }) =
  let
    CP = PM.PartialMapPreorder (CodePreorder A) (CodePreorder C)
    module R = ≤-Reasoning CP
    open R using (_≈⟨_⟩_)
  in
  let
    sem≈ =
      let
        step₁ : _≈_ CP
                  (semProg (p ++ q))
                  (semProg q PM.∘p semProg p)
        step₁ = semProg-append p q

        step₂ : _≈_ CP
                  (semProg q PM.∘p semProg p)
                  (g PM.∘p f)
        step₂ =
          comp-≈
            {ℓCon = ℓCode}
            {ℓRel = ℓRel}
            {A = CodePreorder A}
            {B = CodePreorder B}
            {C = CodePreorder C}
            {f = semProg q}
            {f' = g}
            {g = semProg p}
            {g' = f}
            semQ≈g semP≈f
      in
      _≈⟨_⟩_ (semProg (p ++ q))
        {b = semProg q PM.∘p semProg p}
        {c = g PM.∘p f}
        step₁ step₂
  in
  record
    { proj₁ = p ++ q
    ; proj₂ = sem≈
    }

data ProgTag : Set lzero where
  progTag : ProgTag

progTagId : ℕ
progTagId = 27

port2Cat
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Template.Singleton2Cat (ParOnKernels {ℓ} {ℓRel} {ℓCode}) progTagId ProgTag
port2Cat {ℓ} {ℓRel} {ℓCode} =
  LawTemplate.lawSingleton2Cat
    {C = ParOnKernels {ℓ} {ℓRel} {ℓCode}}
    {Tag = ProgTag}
    progTagId
    ProgOb
    (λ {A} {B}
      (h : Con (Thin2Cat.Hom (ParOnKernels {ℓ} {ℓRel} {ℓCode}) A B)) →
      ProgImplementation {ℓ} {ℓRel} {ℓCode} h)
    (λ {A} → idProgImplementation {ℓ} {ℓRel} {ℓCode} {A = A})
    (λ {A} {B} {C₀} {f} {g} pf pg →
      compProgImplementation
        {ℓ} {ℓRel} {ℓCode}
        {A = A} {B = B} {C = C₀}
        {f = f} {g = g}
        pf pg)

ProgDisplayed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (ParOnKernels {ℓ} {ℓRel} {ℓCode}) lzero (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
ProgDisplayed {ℓ} {ℓRel} {ℓCode} = Template.Displayed (port2Cat {ℓ} {ℓRel} {ℓCode})

ParProg
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (ℓCode ⊔ ℓRel)
ParProg {ℓ} {ℓRel} {ℓCode} = Template.WithPort (port2Cat {ℓ} {ℓRel} {ℓCode})

forgetParProg
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (ParProg {ℓ} {ℓRel} {ℓCode})
      (ParOnKernels {ℓ} {ℓRel} {ℓCode})
forgetParProg {ℓ} {ℓRel} {ℓCode} = Template.forget (port2Cat {ℓ} {ℓRel} {ℓCode})

-- Composite forgetful semantics `ParProg → Par`.
semParProg
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (ParProg {ℓ} {ℓRel} {ℓCode})
      (PM.Par {ℓCon = ℓCode} {ℓRel = ℓRel})
semParProg {ℓ} {ℓRel} {ℓCode} =
  forgetParOnKernels {ℓ} {ℓRel} {ℓCode}
    ∘F
  forgetParProg {ℓ} {ℓRel} {ℓCode}
