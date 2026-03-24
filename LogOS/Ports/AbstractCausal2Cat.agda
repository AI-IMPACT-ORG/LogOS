{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractCausal2Cat where

-- Causal physical systems as a law-port over the unrestricted physical kernel
-- category induced by a shared distributed-semantics ledger.
--
-- This is the default irreversibility-facing causal slice:
-- locality of observables is still chosen once through `DependentLocalSemantics`,
-- but physical arrows are arbitrary kernel morphisms over that shared boundary,
-- equipped only with an explicit flow-preservation certificate.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.HomFlow using (KernelHomFlow; idKernelHomFlow; composeKernelHomFlow)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat using
  ( DecoratedHom
  ; mkTotalObjR
  ; mkTotalHomR
  ; base
  ; baseHom
  ; dispHom
  )

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat.Locality as Locality
import LogOS.Ports.LawSlice2Cat as LawSlice
import LogOS.LT.Ports.PortSig as PortSig

module Causal2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level}
  (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  where

  open DependentLocalSemantics PS
  module Local = Locality.Deutsch2CatLocal {ℓCode = ℓCode} PS

  PhysicalKernel : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel ⊔ ℓCode))
  PhysicalKernel = Local.PhysicalKernel

  kernel = Local.kernel

  LOGᵏ : Thin2Cat _ _ _
  LOGᵏ = Local.LOGᵏ

  data CausalTag : Set where
    causalTag : CausalTag

  record CausalOb : Set where
    constructor ttCausal

  module Port =
    LawSlice.Exports
      {C = LOGᵏ}
      {Tag = CausalTag}
      CausalOb
      (λ {A} {B} (h : Con (Thin2Cat.Hom LOGᵏ A B))
        → KernelHomFlow GC GC h)
      (idKernelHomFlow GC)
      (λ ff gg → composeKernelHomFlow ff gg)

  port2Cat : LawSlice.Singleton2Cat LOGᵏ CausalTag
  port2Cat = Port.port2Cat

  open Port public using
    ( singleton
    ; stack
    ; port
    ; Displayed
    ; WithPort
    ; forget
    )

  causalObj : PhysicalKernel → Thin2Cat.Obj WithPort
  causalObj K = mkTotalObjR K ttCausal

  CausalDisplayedHom
    : PhysicalKernel → PhysicalKernel
    → Set
        ( lsuc (ℓI ⊔ ℓOCon)
        ⊔ lsuc (ℓI ⊔ ℓORel)
        ⊔ ℓCode
        ⊔ lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)
        )
  CausalDisplayedHom K K' =
    DecoratedHom Displayed (causalObj K) (causalObj K')

  mkCausalHom
    : ∀ {K K' : PhysicalKernel}
    → (h : Con (Thin2Cat.Hom LOGᵏ K K'))
    → KernelHomFlow GC GC h
    → CausalDisplayedHom K K'
  mkCausalHom h hf =
    mkTotalHomR h hf

  causalKernelOf : Thin2Cat.Obj WithPort → PhysicalKernel
  causalKernelOf X = base {D = Displayed} X

  causalToKernelHom
    : ∀ {A B : Thin2Cat.Obj WithPort}
    → Con (Thin2Cat.Hom WithPort A B)
    → Con (Thin2Cat.Hom LOGᵏ (causalKernelOf A) (causalKernelOf B))
  causalToKernelHom {A} {B} h =
    baseHom {D = Displayed} {X = A} {Y = B} h

  causalFlowWitness
    : ∀ {A B : Thin2Cat.Obj WithPort}
    → (h : Con (Thin2Cat.Hom WithPort A B))
    → KernelHomFlow GC GC (causalToKernelHom h)
  causalFlowWitness {A} {B} h =
    dispHom {D = Displayed} {X = A} {Y = B} h

open Causal2CatLocal public using
  ( PhysicalKernel
  ; kernel
  ; LOGᵏ
  ; CausalTag
  ; CausalOb
  ; port2Cat
  ; singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  ; causalObj
  ; CausalDisplayedHom
  ; mkCausalHom
  ; causalKernelOf
  ; causalToKernelHom
  ; causalFlowWitness
  )
