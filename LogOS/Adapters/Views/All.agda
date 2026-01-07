{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Views.All where

-- Canonical transport/adaptation surfaces:
-- - signature maps (reindexing “views”)
-- - kernel morphisms over signature maps
-- - semantic presentation adapters (interlingua)
-- - computation/process morphisms (SchemeCategory)

open import LogOS.Prelude

open import LogOS.Base.Signature public
open import LogOS.Base.Signature.Hom public

open import LogOS.Kernel.Reindex public
open import LogOS.Kernel.HomOverSig public

open import LogOS.Ports.Semantic.Interlingua public
open import LogOS.Adapters.Views.SatMor public
open import LogOS.Adapters.Views.SystemIO public

-- Avoid a name clash with `LogOS.Computation.Scheme.run≤` when combining
-- “schemes” and “processes” in a single import surface.
open import LogOS.Computation.SchemeCategory public hiding (run≤)
