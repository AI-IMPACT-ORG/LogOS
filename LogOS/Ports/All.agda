{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.All where

-- Ports (hexagonal boundary interfaces).
--
-- This directory contains *port interfaces* (Agda records) for the “outside
-- world” of the logical-transformer core.
--
-- Examples of intended ports:
-- - observation ports (what is allowed to be observed at a boundary)
-- - locality ports (families of local probes combined into a pointwise boundary)
-- - input/output ports (admissible inputs; outputs + telemetry as observations)
-- - causality/normalisation ports (guarded closures, stable-point boundaries)
-- - cost/grade ports (assumption-scoped, not baked into the kernel)
-- - translation ports (presentation relabellings, boundary-preserving maps)
--
-- Rule of thumb: a port should depend only on the LT core (`LogOS/LT/**`) and
-- base (`LogOS/Prelude.agda`, `LogOS/Syntax/**`), never on `LogOS/Adapters/**`
-- or `LogOS/Apps/**` (adapters/apps may depend on ports, never the other way
-- around).
--
-- Stable downstream entrypoints live in the curated API surface:
-- - dependent-first ports: `LogOS/API/Ports/Dependent.agda`
