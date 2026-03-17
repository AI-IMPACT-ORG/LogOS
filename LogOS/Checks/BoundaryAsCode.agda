{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.BoundaryAsCode where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
import LogOS.LT.Theorems.Centering as Centering
import LogOS.Ports.BoundaryAsCode as BoundaryAsCode

data Region : Set where
  here : Region

O : Region → ConPreorder lzero lzero
O _ = UnitPreorder₀

P = BoundaryAsCode.boundaryPort Region O

manualPackage : BoundaryAsCode.TransparentDenotationPackage P
manualPackage =
  BoundaryAsCode.mkTransparentDenotationPackage
    (BoundaryAsCode.denote P)
    (BoundaryAsCode.denoteBoundaryTransparent P)

canonicalPackage : BoundaryAsCode.TransparentDenotationPackage P
canonicalPackage =
  BoundaryAsCode.canonicalTransparentDenotationPackage P

fiber
  : Centering.ContractibleFiber
      (BoundaryAsCode.TransparentDenotationPackage P)
      BoundaryAsCode.TransparentDenotationPackage≈
fiber = BoundaryAsCode.transparentDenotationFiber P

packageContractsToCenter
  : BoundaryAsCode.TransparentDenotationPackage≈
      manualPackage
      canonicalPackage
packageContractsToCenter =
  Centering.contract fiber manualPackage

packageNoFork
  : BoundaryAsCode.TransparentDenotationPackage≈
      manualPackage
      canonicalPackage
packageNoFork =
  BoundaryAsCode.transparentDenotationNoFork P
    {x = manualPackage}
    {y = canonicalPackage}
