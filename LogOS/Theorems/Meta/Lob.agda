{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Lob where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Theorems.Meta.Assumptions.Core public using (Provability; ProvabilityOps; HBLClassic)
open import LogOS.Theorems.Meta.Assumptions.Diagonal public using (Diagonalization)

-- Packaging for Löb’s theorem (assumption‑based, schematic):
-- We intentionally do not fix a concrete syntax or evaluator. Instead, models
-- provide a code‑level implication operator and the Hilbert–Bernays–Löb
-- derivability conditions as assumptions, then obtain the Löb schema.

-- Classic HBL and diagonalization assumptions are now provided from Assumptions.

-- Conditional Löb schema packaged as an assumption: provide this to obtain Gödel 2.

record LoebAxiom {ℓ}
                 {Sig : LogOS.Base.Signature.LogOSSignature ℓ}
                 {Q : LogOS.Minimal.Adapter.QAdapter ℓ}
                 (K  : LogOS.Kernel.Kernel Sig Q)
                 (Pr : Provability K)
                 (Op : ProvabilityOps K)
                 : Set (lsuc ℓ) where
  open Kernel K
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    loeb
      : (φ  : Code)
      → ⊢ (Imp (Box φ) φ)
      → ⊢ φ

-- Optional bridge: package the standard HBL + diagonalization into a
-- LoebAxiom. In many classical developments, Loeb is derivable from these.
-- We expose this as an assumption record (users can instantiate it to stay
-- close to the literature without changing downstream uses).

record LoebFromHBL {ℓ}
                   {Sig : LogOS.Base.Signature.LogOSSignature ℓ}
                   {Q : LogOS.Minimal.Adapter.QAdapter ℓ}
                   (K  : LogOS.Kernel.Kernel Sig Q)
                   (Pr : Provability K)
                   (Op : ProvabilityOps K)
                   (Hb : HBLClassic K Pr Op)
                   (Dl : Diagonalization K Pr Op)
                   : Set (lsuc ℓ) where
  field
    asLoeb : LoebAxiom K Pr Op

-- Gödel 2 (conditional): If Con ≡ (□⊥ → ⊥) and the model is consistent (¬ Prov ⊥),
-- then Con is not provable. This uses loeb and equality transport only.

godel2
  : ∀ {ℓ} {Sig : LogOS.Base.Signature.LogOSSignature ℓ}
    {Q : LogOS.Minimal.Adapter.QAdapter ℓ}
    (K  : LogOS.Kernel.Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (L  : LoebAxiom K Pr Op)
    (Bot Con : LogOS.Kernel.Kernel.Code K)
    (ConDef  : Con ≡ ProvabilityOps.Imp Op (ProvabilityOps.Box Op Bot) Bot)
    (Consistent : ¬ (Provability.Prov Pr Bot))
  → ¬ (Provability.Prov Pr Con)
godel2 K Pr Op L Bot Con ConDef Consistent pCon =
  let
    open Provability Pr using (Prov)
    open ProvabilityOps Op
    -- Transport Prov Con along ConDef to get Prov (Imp (Box Bot) Bot)
    pImp : Prov (Imp (Box Bot) Bot)
    pImp = subst (λ x → Prov x) ConDef pCon
    -- Löb with φ = Bot yields Prov Bot
    pBot : Prov Bot
    pBot = LoebAxiom.loeb L Bot pImp
  in Consistent pBot
