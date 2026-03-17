{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Minimal where

-- Minimal, stable entrypoint for first-time contributors and downstream users.
--
-- This module is intentionally small:
-- - `Core` provides the atomic spine (preorders, views, thin 2-categories),
-- - `Kernel` adds the logical-transformer kernel + ports/capabilities surface.

open import LogOS.API.Core public
open import LogOS.API.Kernel public

