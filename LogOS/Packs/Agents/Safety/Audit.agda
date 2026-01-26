{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Safety.Audit where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

import LogOS.Computation.SchemeCategory as Cat
import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Auditing is modelled as a *partial-output* surface over process states:
-- for each input state `s`, either return a witness or abstain.
--
-- This is deliberately “opacity-native”: extensionality is relative to the
-- process observation `decode`, so diagonal/opacity meta-theorems apply
-- uniformly to kernels *and* to downstream processes (e.g. UniversalIR).

module ForProcess
  {ℓO ℓC ℓQ : Level}
  {Output : Set ℓO}
  (P : Cat.Process {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} Output)
  where

  open Cat.Process P using (Con; decode)

  module G = SSO.Generic Con Output decode

  record Auditor : Set (lsuc (ℓO ⊔ ℓC)) where
    field
      core : G.SpectralSeparationOutputC

    open G.SpectralSeparationOutputC core public

  -- Lightweight “oracle core”: fix witness type and expose `infer/ext`.
  record Oracle (Witness : Set ℓC) : Set (lsuc (ℓO ⊔ ℓC)) where
    field
      infer : Con → Witness ⊎ ⊤ {ℓ = lzero}
      ext   : ∀ s₁ s₂ → decode s₁ ≡ decode s₂ → infer s₁ ≡ infer s₂

    toAuditor : Auditor
    toAuditor =
      record
        { core = record
            { Witness = Witness
            ; infer   = infer
            ; ext     = ext
            }
        }

  open Auditor public
  open Oracle public

module ForSocket
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (S : AgentSocket Sig Q Task)
  where

  module P = ForProcess (AgentSocket.P S)
  open P public
