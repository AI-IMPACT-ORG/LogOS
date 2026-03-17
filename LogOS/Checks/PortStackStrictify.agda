{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.PortStackStrictify where

-- Guardrail: ensure `PortStack.ClassicalLimit.strictifyStack` stays usable.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.ConPreorder.Antisymmetry using (Antisymmetry)
open import LogOS.LT.Kernel using (Kernel; BoundaryKernel; decode)
open import LogOS.LT.Hom as Hom using (KernelHom; idKernelHom; mapCode; map∂)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)

open import LogOS.LT.DisplayedThin2Cat using
  ( DecoratedThin2Cat
  ; DecoratedHom
  ; mkTotalObjR
  ; baseHom
  )
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; mapHom)

import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.PortStack.ClassicalLimit as PSC
import LogOS.LT.LOG.Contract2Cat as Contract2Cat
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode2Cat

unitAntisym : Antisymmetry UnitPreorder₀
unitAntisym =
  record
    { antisym = λ { {x = ttℓ} {y = ttℓ} _ _ → refl }
    }

K : Kernel lzero lzero lzero
K = BoundaryKernel UnitPreorder₀

-- A minimal 1-port stack: contracts.
ContractStack : PortStack.PortStack (LOG {lzero} {lzero} {lzero})
ContractStack =
  Contract2Cat.stack {ℓ = lzero} {ℓRel = lzero} {ℓCode = lzero}

private
  DomStack = PSC.withClassicalLimit ContractStack
  CodStack = PSC.withStrictDecode ContractStack

  DomDisplayed = PortStack.StackDisplayed DomStack
  CodDisplayed = PortStack.StackDisplayed CodStack

  DomCat = DecoratedThin2Cat DomDisplayed
  CodCat = DecoratedThin2Cat CodDisplayed

  F : Thin2Functor DomCat CodCat
  F = PSC.strictifyStack ContractStack

  module Dom = Thin2Cat DomCat

  Xdom : Dom.Obj
  Xdom = mkTotalObjR K (unitAntisym , ttℓ)

  fdom : DecoratedHom DomDisplayed Xdom Xdom
  fdom = Dom.id {A = Xdom}

  strictCap : PSC.HasStrictDecode CodStack
  strictCap =
    record
      { hasPort =
          PortStack.hasHead
      }

  strictifiedMor : DecoratedHom CodDisplayed (Thin2Functor.mapObj F Xdom) (Thin2Functor.mapObj F Xdom)
  strictifiedMor = mapHom F {A = Xdom} {B = Xdom} fdom

  strictifiedHom : KernelHom K K
  strictifiedHom = baseHom strictifiedMor

  strictifiedLaw : StrictDecode2Cat.StrictDecodeLaw strictifiedHom
  strictifiedLaw =
    PSC.strictDecodeLawOf
      {ℓ = lzero} {ℓRel = lzero} {ℓCode = lzero}
      {S = CodStack}
      strictCap
      {X = Thin2Functor.mapObj F Xdom}
      {Y = Thin2Functor.mapObj F Xdom}
      strictifiedMor

-- Use the strict decode law once (CI regression test).
_ : decode K (mapCode strictifiedHom ttℓ) ≡ map∂ strictifiedHom (decode K ttℓ)
_ = strictifiedLaw ttℓ
