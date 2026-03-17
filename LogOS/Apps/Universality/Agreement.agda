{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.Agreement where

-- Split into submodules:
-- - `Agreement.Universal` : the generic measured agreement family
-- - `Agreement.Task`      : `PATask` encodings instantiating that family
-- - `Agreement.ExprTask`  : `PAExprTask` encodings instantiating that family
-- - `Agreement.Stack`     : derived observations for the stacked adapter

import LogOS.Apps.Universality.Agreement.Universal as Universal
import LogOS.Apps.Universality.Agreement.Task as Task
import LogOS.Apps.Universality.Agreement.ExprTask as ExprTask
import LogOS.Apps.Universality.Agreement.Stack as Stack

open Universal public
open Task public
open ExprTask public
open Stack public
