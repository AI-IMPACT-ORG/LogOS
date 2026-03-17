{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Core where

-- Boundary preorder + constructor views for the concrete ZF/ZFC proof semantics.

import LogOS.Apps.ZFC.Proof.Semantics.Core.ModelDef as ModelDef
import LogOS.Apps.ZFC.Proof.Semantics.Core.ModelCoreDef as ModelCoreDef

open ModelDef public
open ModelCoreDef public
