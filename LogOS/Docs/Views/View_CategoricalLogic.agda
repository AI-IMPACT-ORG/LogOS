{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Docs.Views.View_CategoricalLogic where

-- Typechecked “view surface” for the categorical-logic presentation.
--
-- Keep this module intentionally lightweight: it should be importable alongside
-- other views/tests without introducing operator/name clashes.

open import LogOS.Prelude public
