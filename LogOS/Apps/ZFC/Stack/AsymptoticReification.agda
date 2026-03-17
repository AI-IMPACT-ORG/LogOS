{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification where

-- “Asymptotic” self-similarity for set-theoretic stacks.
--
-- This module packages a precise version of the following design idea:
--
--   sets  --(membership observation)-->  predicates
--     ^                               |
--     |                               v
--   reify (up to Flow)           observability doctrine
--
-- The key point is epistemic honesty: a reification step is only assumed *up
-- to a chosen guarded closure* (`Flow`). The “classical” equalities one expects
-- in ZF are recovered only once the relevant predicates are stable points of
-- that doctrine.
--
-- Note: the slogan “`Flow = id`” is only defensible when predicate reification
-- is *not* total/unrestricted. If one can reify *every* predicate and also take
-- `Flow = id`, then Russell-style diagonalisation (i.e. unbounded
-- comprehension) is available. In this repository, the restricted-by-default
-- reification interface makes this dependency explicit.
--
-- Physicist’s mnemonic (only a mnemonic):
-- `Flow` is the observation/normalisation step, and stability is “already at
-- the asymptote”. Reification turns a (normalised) predicate into a set whose
-- membership behaviour matches the observed predicate.

import LogOS.Apps.ZFC.Stack.AsymptoticReification.ReificationPort as ReificationPort
import LogOS.Apps.ZFC.Stack.AsymptoticReification.StagedAdmissibility as StagedAdmissibility
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CoreFromReification as CoreFromReification
import LogOS.Apps.ZFC.Stack.AsymptoticReification.FOFromReification as FOFromReification
import LogOS.Apps.ZFC.Stack.AsymptoticReification.LocalPresentationFO as LocalPresentationFO
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageReificationPort as CrossStageReificationPort
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageFOFromReification as CrossStageFOFromReification
import LogOS.Apps.ZFC.Stack.AsymptoticReification.GuardedLawvere as GuardedLawvere

open ReificationPort public
open StagedAdmissibility public
open CoreFromReification public
open FOFromReification public
open LocalPresentationFO public
open CrossStageReificationPort public
open CrossStageFOFromReification public
open GuardedLawvere public
