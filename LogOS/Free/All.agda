{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Free.All where

-- Umbrella module for free constraint syntax layers.
--
-- We re-export the modules under short aliases (rather than re-exporting their
-- contents), because the three layers intentionally share many identifiers.

open import LogOS.Free.Constraints as Constraints public using ()
open import LogOS.Free.ConstraintsIndexed as ConstraintsIndexed public using ()
open import LogOS.Free.ConstraintsOverSig as ConstraintsOverSig public using ()
