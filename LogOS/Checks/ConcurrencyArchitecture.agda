{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ConcurrencyArchitecture where

open import LogOS.Prelude

import LogOS.Apps.Concurrency.HappensBefore as HB

sharedBoundarySemantics = HB.HBPhysicalSemantics

dependentStackTransport = HB.sharedBoundaryTransport

sharedBoundaryRaceFreeWitness = HB.safe-raceFree

sharedBoundaryRaceCounterexample = HB.not-raceFree-racy
