{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Views where

-- Optional “views” / emergent interpretations on the LT spine.
--
-- These modules are *not* re-exported by the default curated surface
-- (`LogOS.API.LT`). Import this module explicitly when you want these
-- interpretation-level packagings.

open import LogOS.LT.InstitutionFragment public
open import LogOS.LT.PredicateReindexing public
open import LogOS.LT.AbstractKZ public
open import LogOS.LT.Derivability public
open import LogOS.LT.Theory public
open import LogOS.LT.ConPreorder.Discrete public
open import LogOS.LT.ConPreorder.Isomorphism public
open import LogOS.LT.TypeTheory public
