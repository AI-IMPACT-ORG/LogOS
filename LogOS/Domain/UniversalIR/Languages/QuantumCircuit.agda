{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Languages.QuantumCircuit where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Task using (PATask; eval)
open import LogOS.Domain.UniversalIR.Backend using (Backend; mkBackend)
open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.Encoding public using (incBits; natToBits; length)
open import LogOS.Domain.UniversalIR.IR using (observe)
open import LogOS.Domain.UniversalIR.IR using (lowerToIR; decode; take; bitsToNat)
import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky
open import LogOS.Domain.UniversalIR.Std using (decodeChurch-church)
open import LogOS.Domain.UniversalIR.Encoding as Enc using (take-length; bitsToNat-natToBits)

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)

-- A minimal “explicit circuit” backend:
-- - circuit syntax is a list of gate instructions (`QCInstr`)
-- - semantics is deterministic on basis states (`Wires = List Bool`)
--
-- For the production UniversalIR pipeline we keep the brand compiler *fast and
-- extensional*: the output wires are initialised to the binary encoding of
-- `eval t`, and the program immediately halts. This wires in explicit circuits
-- as a scheme choice without committing to a full reversible arithmetic circuit
-- generator.
--
-- For the scheme-centric universality narrative, use `quantumCircuitMachineScheme`
-- from `LogOS.Domain.UniversalIR.Schemes`; the `run` here is a minimal wrapper.
--
-- If you want an *executable* state-preparation circuit artifact (start from
-- all-zero wires and flip bits), use `compilePrepBrand` below.

zeros : ℕ → Wires
zeros zero    = []
zeros (suc n) = false ∷ zeros n

setBitsProg : ℕ → List Bool → List QCInstr
setBitsProg _ []            = []
setBitsProg i (false ∷ ws)  = QNOP ∷ setBitsProg (suc i) ws
setBitsProg i (true  ∷ ws)  = QX i ∷ setBitsProg (suc i) ws

progSetBits : List Bool → List QCInstr
progSetBits ws = setBitsProg 0 ws

compileBrand : PATask → QuantumCircuitCode
compileBrand t =
  let
    ws = natToBits (eval t)
  in
  mkQC 0 (length ws) ws (QCHALT ∷ [])

compilePrepBrand : PATask → QuantumCircuitCode
compilePrepBrand t =
  let
    ws = natToBits (eval t)
  in
  mkQC 0 (length ws) (zeros (length ws)) (progSetBits ws)

backend : Backend PATask QuantumCircuitCode
backend = mkBackend compileBrand UQC

compile : PATask → UCode
compile t = Backend.toUCode backend t

fuel : PATask → ℕ
fuel _ = 0

fuelPrep : PATask → ℕ
fuelPrep t = length (natToBits (eval t))

exec : ℕ → PATask → UCode
exec n t = Backend.exec backend n t

toIR : PATask → UCode
toIR t = Backend.toIRAt backend (fuel t) t

run : PATask → ℕ
run t = Backend.decodeAt backend (fuel t) t

-- ============================================================================
-- Circuit families (uniform-by-bound)
--
-- A single finite circuit cannot express unbounded memory. The clean way to
-- include “circuits as a computation paradigm” in a universality story is as a
-- *family* indexed by a resource bound (time/size).
--
-- Here we provide the minimal, explicit family interface:
-- for a bound `k`, build a (deterministic, basis-state) circuit that exposes the
-- observable result of running some `UCode` for `k` steps.
--
-- This is intentionally simple (compile-by-observation under a step budget), but it is honest and
-- snaps directly into the Scheme view: “machines are schemes”.
-- ============================================================================

compileFamilyFromU : ℕ → UCode → QuantumCircuitCode
compileFamilyFromU k u =
  let
    n  = observe (simulate k u)
    ws = natToBits n
  in
  mkQC 0 (length ws) ws (QCHALT ∷ [])

compileFamilyFromMinsky : ℕ → PATask → QuantumCircuitCode
compileFamilyFromMinsky k t = compileFamilyFromU k (Minsky.compile t)

observe-familyFromU : ∀ k u → observe (UQC (compileFamilyFromU k u)) ≡ observe (simulate k u)
observe-familyFromU k u =
  let
    n  = observe (simulate k u)
    ws = natToBits n
    q  = mkQC 0 (length ws) ws (QCHALT ∷ [])
    m  = bitsToNat (take (length ws) ws)
  in
  trans
    (decodeChurch-church m)
    (trans
      (cong bitsToNat (take-length ws))
      (bitsToNat-natToBits n))
