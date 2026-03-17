{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ArchitecturalNormalForm where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.Coherence using (approx)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( ProductDisplayed
  ; DecoratedThin2Cat
  ; DecoratedHom
  ; baseHom
  )

import LogOS.API.Kernel as KernelAPI
import LogOS.API.Theorems.Core as TheoremsAPI
import LogOS.API.Theorems.Strictification as StrictTheoremsAPI
import LogOS.LT.LOG.Boundary2Cat as Boundary2Cat
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat
import LogOS.LT.LOG.Contract2Cat as Contract2Cat
import LogOS.LT.LOG.ClassicalLimit2Cat as ClassicalLimit2Cat
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode2Cat
import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Definitional as PortsAsDisplayedDef

normalForm : TheoremsAPI.ObservationPreservingArchitecturalNormalForm lzero lzero lzero
normalForm = TheoremsAPI.architecturalNormalForm {lzero} {lzero} {lzero}

strictNormalForm : StrictTheoremsAPI.ArchitecturalNormalFormStrictification lzero lzero lzero
strictNormalForm = StrictTheoremsAPI.architecturalNormalFormStrictification {lzero} {lzero} {lzero}

module ANF = TheoremsAPI.ObservationPreservingArchitecturalNormalForm normalForm
module StrictANF = StrictTheoremsAPI.ArchitecturalNormalFormStrictification strictNormalForm
module Layers = PortsAsDisplayedDef.SupportedArchitectureLayers (ANF.supportedArchitectureLayers)

K : KernelAPI.Kernel lzero lzero lzero
K = KernelAPI.BoundaryKernel UnitPreorder₀

decoratedId
  : DecoratedHom
      (Implementation2Cat.ImplementationDisplayed {lzero} {lzero} {lzero})
      (Implementation2Cat.embed K)
      (Implementation2Cat.embed K)
decoratedId = Implementation2Cat.fromFacadeHom (KernelAPI.idKernelHom K)

module G = Thin2Cat (Boundary2Cat.LOGᴳ {lzero} {lzero} {lzero})

baseIdRefines
  : _⊑_ (G.Hom K K)
      (baseHom
        {D = Implementation2Cat.ImplementationDisplayed {lzero} {lzero} {lzero}}
        {X = Implementation2Cat.embed K}
        {Y = Implementation2Cat.embed K}
        decoratedId)
      (baseHom
        {D = Implementation2Cat.ImplementationDisplayed {lzero} {lzero} {lzero}}
        {X = Implementation2Cat.embed K}
        {Y = Implementation2Cat.embed K}
        decoratedId)
baseIdRefines =
  ConPreorder.refl (G.Hom K K)
    {c =
      baseHom
        {D = Implementation2Cat.ImplementationDisplayed {lzero} {lzero} {lzero}}
        {X = Implementation2Cat.embed K}
        {Y = Implementation2Cat.embed K}
        decoratedId}

_ : KernelAPI.KernelHomLike approx K K
    ≡ KernelAPI.KernelHomLikeR approx K K
_ = ANF.kernelHomFactorises K K

_ : StrictANF.toFacadeHom-fromFacadeHom≡id (KernelAPI.idKernelHom K)
    ≡ refl
_ = refl

_ : StrictANF.fromFacadeHom-toFacadeHom≡id decoratedId ≡ refl
_ = refl

_ : _⊑_
      (LogOS.LT.DisplayedThin2Cat.TotalHomPreorder
        (Implementation2Cat.ImplementationDisplayed {lzero} {lzero} {lzero})
        (Implementation2Cat.embed K)
        (Implementation2Cat.embed K))
      decoratedId
      decoratedId
_ = ANF.base⊑→total⊑
      (Implementation2Cat.ImplementationDisplayed {lzero} {lzero} {lzero})
      {X = Implementation2Cat.embed K}
      {Y = Implementation2Cat.embed K}
      {f = decoratedId}
      {g = decoratedId}
      baseIdRefines

_ : Implementation2Cat.LOGᴳʳ {lzero} {lzero} {lzero}
    ≡
    DecoratedThin2Cat (Implementation2Cat.ImplementationDisplayed {lzero} {lzero} {lzero})
_ = Layers.implementation

_ : Thin2Functor
      (DecoratedThin2Cat
        (ProductDisplayed
          (ClassicalLimit2Cat.ClassicalLimitDisplayed {lzero} {lzero} {lzero})
          (Contract2Cat.ContractDisplayed {lzero} {lzero} {lzero})))
      (DecoratedThin2Cat
        (ProductDisplayed
          (StrictDecode2Cat.Displayed {lzero} {lzero} {lzero})
          (Contract2Cat.ContractDisplayed {lzero} {lzero} {lzero})))
_ = StrictANF.strictifyDisplayed {D = Contract2Cat.ContractDisplayed {lzero} {lzero} {lzero}}
