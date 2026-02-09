{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.FOL.All where

open import LogOS.ObjectLogic.FOL.Syntax public
open import LogOS.ObjectLogic.FOL.Subst public
open import LogOS.ObjectLogic.FOL.Semantics public
open import LogOS.ObjectLogic.FOL.ND public
open import LogOS.ObjectLogic.FOL.NDTheory public
open import LogOS.ObjectLogic.FOL.Soundness public

-- Classical axioms are an explicit add-on: see `LogOS.ObjectLogic.FOL.Classical`
-- or `LogOS.ObjectLogic.FOL.AllClassical` if you want them bundled.
