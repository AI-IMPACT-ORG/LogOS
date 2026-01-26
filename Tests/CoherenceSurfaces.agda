{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.CoherenceSurfaces where

open import LogOS.API.Kernel
open import LogOS.Theorems.Core as T
import LogOS.Theorems.Boundary.Graded.All as GB
import LogOS.Packs.UniversalIR.Agreement as UAgree
import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation as POI
import LogOS.API.Architecture as Arch

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

satS↔Form' : _
satS↔Form' = T.Boundary.SatS↔Form

code→form-flowcode' : _
code→form-flowcode' = T.Boundary.Code→Form-FlowCode

-- Graded quick wins: operational iteration bounds and saturation absorption.

step-iteration≤sat' : _
step-iteration≤sat' = GB.step-iteration≤sat

saturation-absorption' : _
saturation-absorption' = GB.saturation-absorption

step-power-law' : _
step-power-law' = GB.step-power-law

-- Core science surfaces used in the Nature-facing narrative.

five-paradigm-agreement' : _
five-paradigm-agreement' = UAgree.five-paradigm-agreement

merge-implies-entropy-increase' : _
merge-implies-entropy-increase' = POI.merge-implies-entropy-increase

irreversible-io-cost-lower-bound' : _
irreversible-io-cost-lower-bound' = POI.irreversible-io-cost-lower-bound

-- Ports/adapters spine: keep the canonical navigation surface stable.

idSatMor' : _
idSatMor' = Arch.Ports.idSatMor

composeSatMor' : _
composeSatMor' = Arch.Ports.composeSatMor

rebaseSystemIO' : _
rebaseSystemIO' = Arch.Tooling.rebase

rebaseSystemIOAlongSatMor' : _
rebaseSystemIOAlongSatMor' = Arch.Tooling.rebaseAlongSatMor

proofsystem-pullback' : _
proofsystem-pullback' = Arch.Tooling.pullback

proofsystem-lift' : _
proofsystem-lift' = Arch.Tooling.liftProofSystem
