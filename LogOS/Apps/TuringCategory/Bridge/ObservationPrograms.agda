{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge.ObservationPrograms where

-- A compositional “partiality enters with observation” bridge.
--
-- Reading:
-- - start from the structural total-map interpretation `codeToPar : LOG → Par`,
-- - add explicit observation ports from `Bridge/KernelToPar.agda`,
-- - compose those ports with total kernel steps as typed programs,
-- - then decorate the reindexed `Par` with those programs via Σ-totalisation.
--
-- Public surface:
-- - explicit observation gates (`ObsGate`, `mkObsGate`)
-- - program syntax/semantics (`Atom`, `Prog`, `semAtom`, `semProg`)
-- - the displayed semantics (`ParProg`, `semParProg`)
-- - constructors that embed total steps and explicit observation ports

import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.Types as Types
-- Public story: observation gates and typed program syntax.
open Types public using
  ( ObsGate
  ; mkObsGate
  ; Atom
  ; run
  ; observe
  ; Prog
  ; _∷_
  ; []
  ; _++_
  ; semAtom
  ; semProg
  )
import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.ParOnKernels as ParOnKernels
-- Support layer: the base `Par` semantics over kernels.
open ParOnKernels public using
  ( ParOnKernels )
import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.ProgDisplayed as ProgDisplayed
-- Public story: displayed semantics of programs over `Par`.
open ProgDisplayed public using
  ( ParProg
  ; semParProg )
import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.Constructors as Constructors
-- Public story: the canonical constructors that tie total steps to observation.
open Constructors public using
  ( runProg
  ; observeProg
  ; embedLOG
  ; runThenObservePort
  ; runThenObserve
  )
