{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Soundness.ModelSoundnessDef where

open import LogOS.Prelude using (Level)

import LogOS.Apps.ZFC.Proof.Semantics.Core as Core

import LogOS.Apps.ZFC.Proof.Semantics.Soundness.Logic as Logic
import LogOS.Apps.ZFC.Proof.Semantics.Soundness.ZF as ZF
import LogOS.Apps.ZFC.Proof.Semantics.Soundness.Presentation as Presentation

module ModelSoundness {ℓ : Level} (M : Core.Model {ℓ}) where
  open Logic.ForModel M public
  open ZF.ForModel M public
  open Presentation.ForModel M public

