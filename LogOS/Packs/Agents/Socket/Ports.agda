{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.Ports where

open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)

-- Designated interface “ports” for agent-like open systems.
--
-- This is intentionally minimal: it avoids committing to a particular concrete
-- signature, while making the safety-/oversight-relevant channels explicit.

record AgentPorts {ℓ : Level} (Sig : LogOSSignature ℓ) : Set (lsuc ℓ) where
  open LogOSSignature Sig
  field
    Obs       : Iface
    Act       : Iface
    Reward    : Iface
    Oversight : Iface
    Shutdown  : Iface
    Comm      : Iface

open AgentPorts public

