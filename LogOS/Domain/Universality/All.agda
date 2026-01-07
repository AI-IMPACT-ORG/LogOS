{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.All where

-- Canonical “all surfaces” entrypoint for Universality:
-- core + kernel + adapters/transports + complexity/physics scaffolding.

open import LogOS.Domain.Universality.Adapter public
open import LogOS.Domain.Universality.Lemmas public

import LogOS.Domain.Universality.RiceTransport as URice
module RiceTransport where
  open URice public

import LogOS.Domain.Universality.BodyEqTransport as UBodyEq
module BodyEqTransport where
  open UBodyEq public

