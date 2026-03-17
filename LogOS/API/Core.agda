{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Core where

open import LogOS.Prelude public
open import LogOS.Syntax.Prop public
open import LogOS.LT.ConPreorder public
open import LogOS.LT.ConPreorder.Indexed public using (IndexedConPreorder; mkIndexedConPreorder; atCP)
open import LogOS.LT.FunPreorder public
open import LogOS.LT.View public
open import LogOS.LT.Thin2Cat public
open import LogOS.LT.Thin2Functor public

-- Discipline gates (typecheck-only): the LT core spine must remain atomic.
-- Exports only one harmless witness.
open import LogOS.LT.Discipline.AtomicSpine public renaming (ok to ltAtomicSpine-ok)
