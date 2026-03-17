{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.MetamathStyle where

-- Worked example: close the ZF-core proof ledger as a Metamath-style database.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

import LogOS.Ports.Metamath as MM

import LogOS.Apps.ZFC.Proof.Syntax as Syntax
open Syntax
import LogOS.Apps.ZFC.Proof.Axioms as Axioms
open Axioms
-- Labels: either a bundled core axiom instance, or a concrete modus-ponens step.
data ZFCLabel : Set where
  axL : ∀ {φ} → TheoryAxiom φ → ZFCLabel
  mpL : (φ ψ : Formula) → ZFCLabel

hypsL : ZFCLabel → List Formula
hypsL (axL _) = []
hypsL (mpL φ ψ) = (φ ⇒ ψ) ∷ φ ∷ []

conclL : ZFCLabel → Formula
conclL (axL {φ} _) = φ
conclL (mpL φ ψ) = ψ

DB : MM.Database Formula
DB =
  record
    { Label = ZFCLabel
    ; hyps  = hypsL
    ; concl = conclL
    }

module P = MM.FromDB DB
open P
-- No hidden base axioms: everything is in the database labels.
Base : Formula → Set
Base _ = ⊥

-- Empty local ledger: global axioms come from `axL`.
Ledger : Theory
Ledger _ = ⊥

-- Example: a core ZF axiom is derivable by applying its label as a 0-premise rule.
extensionality-derivable : DerivesR Base Ledger extensionalityF
extensionality-derivable =
  ruleT (axL (axZFCore axExtensionality)) all[]
