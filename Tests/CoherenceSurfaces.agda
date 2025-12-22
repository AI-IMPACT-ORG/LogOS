{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.CoherenceSurfaces where

open import LogOS.API.Minimal
open import LogOS.Theorems.Core as T
import LogOS.Theorems.Boundary.Graded.All as GB

-- Coherence regression: ensure the curated public surfaces keep exporting
-- the “textbook name” aliases and key lemma entrypoints.

park-induction' : _
park-induction' = T.Boundary.park-induction

least-prefixed-point' : _
least-prefixed-point' = T.Boundary.least-prefixed-point

scott-continuity-K' : _
scott-continuity-K' = T.Boundary.scott-continuity-K

kleene-approximation-K' : _
kleene-approximation-K' = T.Boundary.kleene-approximation-K

fixedpoint-eq-under-antisym' : _
fixedpoint-eq-under-antisym' = fixedpoint-eq-under-antisym

finite-convergence-equalities' : _
finite-convergence-equalities' = T.Boundary.finite-convergence-equalities

flowcode-mono-decode' : _
flowcode-mono-decode' = T.Code.flowcode-mono-decode

reify-idempotent-decode' : _
reify-idempotent-decode' = T.Boundary.reify-idempotent-decode

-- Graded quick wins: operational iteration bounds and saturation absorption.

step-iteration≤sat' : _
step-iteration≤sat' = GB.step-iteration≤sat

saturation-absorption' : _
saturation-absorption' = GB.saturation-absorption

step-power-law' : _
step-power-law' = GB.step-power-law

