{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.MetaLanguage.All where

-- Polymorphic meta-language surface:
-- - schemes/processes + their categorical structure
-- - a functorial contract language over signatures
-- - open-system network operations (cospans/boundaries)
--
-- This is core infrastructure (not an “application pack”); it is used by the
-- Universality story but is not specific to it.

module Scheme where
  open import LogOS.Computation.Scheme public

module SchemeCategory where
  open import LogOS.Computation.SchemeCategory public

module KernelAsProcess where
  open import LogOS.Computation.KernelUniversalProcess public

module FunctorialContracts where
  open import LogOS.Minimal.ConstraintsOverSig public

module OpenSystems where
  open import LogOS.Base.Signature public
  open import LogOS.Base.Signature.Hom public
  open import LogOS.Base.Ops.Boundary public
  open import LogOS.Base.Ops.Cospan public
