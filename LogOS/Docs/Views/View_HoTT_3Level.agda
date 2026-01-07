{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Docs.Views.View_HoTT_3Level where

-- Typechecked “view surface” for the 3-level HoTT-style reading (S/H/G).
--
-- Keep this module lightweight to avoid name clashes when imported alongside
-- other views/tests.

open import LogOS.Prelude public
