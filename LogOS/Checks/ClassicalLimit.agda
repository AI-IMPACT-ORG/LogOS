{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ClassicalLimit where

-- Guardrail: ensure `Ports.ClassicalLimit` stays usable as an explicit strictifier.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.Kernel using (Kernel; BoundaryKernel; decode)
import LogOS.LT.Hom as Hom
import LogOS.LT.Hom.Strictification as StrictHom
open import LogOS.Ports.ClassicalLimit using (Antisymmetry; strictifyKernelHom)

open import LogOS.LT.DisplayedThin2Cat using
  ( ProductDisplayed
  ; DecoratedThin2Cat
  ; DecoratedHom
  ; mkTotalObjR
  ; baseHom
  ; dispHom
  )
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; mapHom)
import LogOS.LT.LOG.ClassicalLimit2Cat as ClassicalLimit2Cat
import LogOS.LT.LOG.Contract2Cat as Contract2Cat
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode2Cat

unitAntisym : Antisymmetry UnitPreorder₀
unitAntisym =
  record
    { antisym = λ { {x = ttℓ} {y = ttℓ} _ _ → refl }
    }

K : Kernel lzero lzero lzero
K = BoundaryKernel UnitPreorder₀

h : Hom.KernelHom K K
h = Hom.idKernelHom K

h≡ : StrictHom.KernelHom≡ K K
h≡ = strictifyKernelHom unitAntisym h

-- Use the strict `decode-mapCode : ≡` once (CI regression test).
_ : ∀ γ → decode K (StrictHom.mapCode h≡ γ) ≡ StrictHom.map∂ h≡ (decode K γ)
_ = StrictHom.decode-mapCode≡ h≡

-- Guardrail: strictification threads through displayed port layers.
--
-- Here we exercise the generic `strictifyDisplayed` bridge on the contract layer
-- (LOG∂), and use the resulting strict decode law once.

private
  D =
    Contract2Cat.ContractDisplayed {ℓ = lzero} {ℓRel = lzero} {ℓCode = lzero}

  CL =
    ClassicalLimit2Cat.ClassicalLimitDisplayed {ℓ = lzero} {ℓRel = lzero} {ℓCode = lzero}

  SD =
    StrictDecode2Cat.Displayed {ℓ = lzero} {ℓRel = lzero} {ℓCode = lzero}

  DomDisplayed = ProductDisplayed CL D
  CodDisplayed = ProductDisplayed SD D

  DomCat =
    DecoratedThin2Cat DomDisplayed

  CodCat =
    DecoratedThin2Cat CodDisplayed

  F : Thin2Functor DomCat CodCat
  F =
    ClassicalLimit2Cat.strictifyDisplayed {ℓ = lzero} {ℓRel = lzero} {ℓCode = lzero} {D = D}

  module Dom = Thin2Cat DomCat

  Xdom : Dom.Obj
  Xdom = mkTotalObjR K (unitAntisym , ttℓ)

  fdom : DecoratedHom DomDisplayed Xdom Xdom
  fdom = Dom.id {A = Xdom}

  strictified : Σ (Hom.KernelHom K K) (λ h' → StrictDecode2Cat.StrictDecodeLaw h')
  strictified =
    let strictifiedMor = mapHom F {A = Xdom} {B = Xdom} fdom in
    baseHom strictifiedMor , fst (dispHom strictifiedMor)

  strictifiedHom : Hom.KernelHom K K
  strictifiedHom = proj₁ strictified

  strictifiedLaw : StrictDecode2Cat.StrictDecodeLaw strictifiedHom
  strictifiedLaw = proj₂ strictified

_ : decode K (Hom.mapCode strictifiedHom ttℓ) ≡ Hom.map∂ strictifiedHom (decode K ttℓ)
_ = strictifiedLaw ttℓ
