{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Applications.Socket where

-- Curated “agent socket” application surface:
-- ports + contracts + socket core + canonical constructors.

open import LogOS.Packs.Agents.Socket.Ports public
open import LogOS.Packs.Agents.Socket.Contracts public
open import LogOS.Packs.Agents.Socket.Core public

module HomOver where
  open import LogOS.Packs.Agents.Socket.HomOver public

module Reindex where
  open import LogOS.Packs.Agents.Socket.Reindex public

module FromLogicCore where
  open import LogOS.Packs.Agents.Socket.FromLogicCore public

module FromKernel where
  open import LogOS.Packs.Agents.Socket.FromKernel public

module FromGradedKernel where
  open import LogOS.Packs.Agents.Socket.FromGradedKernel public

