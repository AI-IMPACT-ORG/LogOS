{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ExtensionalReflection where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _⊑_)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.ConPreorder.Antisymmetry using (Antisymmetry)
open import LogOS.LT.Kernel using (Kernel; BoundaryKernel)
open import LogOS.LT.Hom.Core using (idKernelHom)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; mkTotalObjR
  ; mkTotalHomR
  )

import LogOS.API.Theorems.Strictification as TheoremsAPI
import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode
import LogOS.LT.Theorems.AbstractGaloisConnection as Galois

trivialDisplayed
  : DisplayedThin2Cat (Kernel2Cat.LOG {lzero} {lzero} {lzero}) lzero lzero
trivialDisplayed =
  record
    { Ob = λ _ → ⊤
    ; HomD = λ _ _ _ → ⊤
    ; idD = λ _ → tt
    ; compD = λ _ _ → tt
    }

topUnique : ∀ {x y : ⊤ {lzero}} → x ≡ y
topUnique {ttℓ} {ttℓ} = refl

antiUnit : Antisymmetry UnitPreorder₀
antiUnit = record { antisym = λ _ _ → topUnique }

K : Kernel lzero lzero lzero
K = BoundaryKernel UnitPreorder₀

X
  : TheoremsAPI.ObservationObj trivialDisplayed
X = mkTotalObjR K (antiUnit , tt)

Y
  : TheoremsAPI.ExtensionalObj trivialDisplayed
Y = mkTotalObjR K (antiUnit , (StrictDecode.strictDecodeUnit , tt))

reflection
  : TheoremsAPI.FiberwiseExtensionalReflection trivialDisplayed
reflection = TheoremsAPI.fiberwiseExtensionalReflection {D = trivialDisplayed}

module ER = TheoremsAPI.FiberwiseExtensionalReflection reflection

include
  : Thin2Functor
      (TheoremsAPI.ExtensionalFiber trivialDisplayed)
      (TheoremsAPI.ObservationFirstFiber trivialDisplayed)
include = ER.include

reflect
  : Thin2Functor
      (TheoremsAPI.ObservationFirstFiber trivialDisplayed)
      (TheoremsAPI.ExtensionalFiber trivialDisplayed)
reflect = ER.reflect

obsId
  : Con (TheoremsAPI.ObservationHomPreorder trivialDisplayed X Y)
obsId = mkTotalHomR (idKernelHom K) (tt , tt)

extId
  : Con (TheoremsAPI.ExtensionalHomPreorder trivialDisplayed X Y)
extId = Galois.L (ER.homReflection X Y) obsId

_ : _⊑_
      (TheoremsAPI.ObservationHomPreorder trivialDisplayed X Y)
      obsId
      (Galois.R (ER.homReflection X Y) extId)
_ = ER.reflectionUnit X Y obsId

_ : _⊑_
      (TheoremsAPI.ExtensionalHomPreorder trivialDisplayed X Y)
      (Galois.L (ER.homReflection X Y) (Galois.R (ER.homReflection X Y) extId))
      extId
_ = ER.reflectionCounit X Y extId
