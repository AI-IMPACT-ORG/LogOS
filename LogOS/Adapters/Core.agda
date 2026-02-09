{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Core where

-- Core view/adaptation surfaces (no tooling I/O).

open import LogOS.Base.Signature public
open import LogOS.Base.Signature.Hom public

open import LogOS.Kernel.Reindex public
open import LogOS.Kernel.HomOverSig public

open import LogOS.Ports.Semantic.Interlingua public
open import LogOS.Adapters.Views.SatMor public

