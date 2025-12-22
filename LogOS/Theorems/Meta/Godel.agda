{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Godel where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Theorems.Meta.Assumptions.Core using (Provability; ProvabilityOps; HBLClassic)
open import LogOS.Theorems.Meta.Assumptions.Diagonal using (Diagonalization)
open import LogOS.Theorems.Meta.Lob as L

-- Conditional Gödel-style incompleteness via Löb packaging: if the model provides
-- a provability predicate `Pr`, operations `Op`, the HBL derivability conditions,
-- and the Löb axiom, then with a chosen bottom `Bot` and its consistency, the
-- usual “Con is unprovable” conclusion follows.

incompleteness
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (Lob : L.LoebAxiom K Pr Op)
    (Bot Con : Kernel.Code K)
    (ConDef  : Con ≡ ProvabilityOps.Imp Op (ProvabilityOps.Box Op Bot) Bot)
    (Consistent : ¬ (Provability.Prov Pr Bot))
  → ¬ (Provability.Prov Pr Con)
incompleteness K Pr Op Lob Bot Con ConDef Consistent =
  L.godel2 K Pr Op Lob Bot Con ConDef Consistent

-- Variant that stays even closer to the literature: supply HBL (classic) +
-- Diagonalization, plus a bridge to a Loeb axiom (derivable in many settings),
-- then conclude Gödel 2 as usual.

incompleteness-classical
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (Hb : HBLClassic K Pr Op)
    (Dl : Diagonalization K Pr Op)
    (Bridge : L.LoebFromHBL K Pr Op Hb Dl)
    (Bot Con : Kernel.Code K)
    (ConDef  : Con ≡ ProvabilityOps.Imp Op (ProvabilityOps.Box Op Bot) Bot)
    (Consistent : ¬ (Provability.Prov Pr Bot))
  → ¬ (Provability.Prov Pr Con)
incompleteness-classical K Pr Op Hb Dl Bridge Bot Con ConDef Consistent =
  let Lob = L.LoebFromHBL.asLoeb Bridge in
  L.godel2 K Pr Op Lob Bot Con ConDef Consistent
