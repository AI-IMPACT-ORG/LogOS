{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Docs.Views.View_MultiInstitution where

-- Documentation view: classic model-theoretic framing (institutions), kept
-- aligned with the implemented kernel surface.

open import LogOS.Prelude public

import LogOS.Base.Signature as Sig
import LogOS.Base.Signature.Hom as SigHom
import LogOS.Minimal.Truth as Truth
import LogOS.Kernel as Kernel
import LogOS.Docs.Views.KernelProjection as KernelProjection
