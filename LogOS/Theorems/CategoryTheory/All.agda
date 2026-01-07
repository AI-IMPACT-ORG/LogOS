{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.All where

import LogOS.Theorems.CategoryTheory.WrapperCore as WrapperCoreₜ
import LogOS.Theorems.CategoryTheory.AdjunctionMonads as AdjunctionMonadsₜ
import LogOS.Theorems.CategoryTheory.KernelCat as KernelCatₜ
import LogOS.Theorems.CategoryTheory.Kernel2Cat as Kernel2Catₜ
import LogOS.Theorems.CategoryTheory.Kernel2CatGraded as Kernel2CatGradedₜ
import LogOS.Theorems.CategoryTheory.PortCat as PortCatₜ
import LogOS.Theorems.CategoryTheory.Yoneda as Yonedaₜ

module WrapperCore = WrapperCoreₜ
module AdjunctionMonads = AdjunctionMonadsₜ
module KernelCat = KernelCatₜ
module Kernel2Cat = Kernel2Catₜ
module Kernel2CatGraded = Kernel2CatGradedₜ
module PortCat = PortCatₜ
module Yoneda = Yonedaₜ
