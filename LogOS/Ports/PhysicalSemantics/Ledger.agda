{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PhysicalSemantics.Ledger where

-- Shared dependent-semantics context is now treated as neutral packaged data.
-- The canonical records live in `LogOS.Ports.PhysicalSemantics.Core`; this
-- module remains as the explicit ledger slot and intentionally re-exports
-- nothing.
