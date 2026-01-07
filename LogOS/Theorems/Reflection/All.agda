{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Reflection.All where

-- Reflection is a cross-cutting pattern in LogOS: the library contains several
-- “stabilisation / retraction” operators living on different carriers.
--
-- This module is a lightweight index that keeps those surfaces discoverable
-- and typecheckable from a single entrypoint.

import LogOS.Theorems.Boundary.Reflection as BoundaryReflectionₜ
import LogOS.Theorems.Reflection.Projector as Projectorₜ
import LogOS.Theorems.Reflection.QuanticNucleus as QuanticNucleusₜ
import LogOS.Theorems.Reflection.NucleusMu as NucleusMuₜ
import LogOS.Theorems.Reflection.ForcingSheaves as ForcingSheavesₜ
import LogOS.Theorems.Projective as Projectiveₜ
import LogOS.Theorems.Modal.S4 as ModalS4ₜ
import LogOS.Theorems.CategoryTheory.AdjunctionMonads as AdjunctionMonadsₜ

module BoundaryReflection = BoundaryReflectionₜ
module Projector = Projectorₜ
module QuanticNucleus = QuanticNucleusₜ
module NucleusMu = NucleusMuₜ
module ForcingSheaves = ForcingSheavesₜ
module Projective = Projectiveₜ
module ModalS4 = ModalS4ₜ
module AdjunctionMonads = AdjunctionMonadsₜ
