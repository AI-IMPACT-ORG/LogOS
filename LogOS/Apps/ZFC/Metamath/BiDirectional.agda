{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional where

-- A transformer-native, refinement-first bridge for the Set.MM port.
--
-- Forward direction (existing): Set.MM token rows -> `Formula` via
-- `Interpretation`, including explicit closure of the mandatory frame and
-- normalization of vacuous binders.
--
-- Backward direction (this module): `Formula` -> token rows -> `MM.Database`,
-- with two important boundary conditions made explicit:
-- - decoding `PFormula` back to `Formula` is certified only up to the
--   environment-threaded renaming computed by `toPFormula` + `toFormula`;
-- - row/database interpretation is exact only after the same closure and
--   normalization steps used by `Interpretation`.

import LogOS.Apps.ZFC.Metamath.BiDirectional.Types as Types
import LogOS.Apps.ZFC.Metamath.BiDirectional.Env as Env
import LogOS.Apps.ZFC.Metamath.BiDirectional.Reify as Reify
import LogOS.Apps.ZFC.Metamath.BiDirectional.Rename as Rename
import LogOS.Apps.ZFC.Metamath.BiDirectional.RoundTrip as RoundTrip
import LogOS.Apps.ZFC.Metamath.BiDirectional.TokenDB as DB
import LogOS.Apps.ZFC.Metamath.BiDirectional.Witness as Witness

open Types public
open Env public
open Reify public
open Rename public
open RoundTrip public
open DB public
open Witness public
