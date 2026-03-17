{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Opacity where

-- Explicit optional surface for the opacity pack.
--
-- This is intentionally not re-exported by `LogOS.API.LT`.

open import LogOS.Ports.Opacity public
open import LogOS.Ports.Opacity.Port public
open import LogOS.Ports.Opacity.Factorisation public
open import LogOS.Ports.Opacity.Distinguishability public
open import LogOS.Ports.Opacity.Obstruction public
open import LogOS.Ports.Opacity.Profile public
open import LogOS.Ports.Opacity.FiniteCompression public
