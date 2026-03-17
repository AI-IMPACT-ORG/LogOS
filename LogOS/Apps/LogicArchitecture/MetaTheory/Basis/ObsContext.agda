{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext where

-- MetaTheory — Context = chosen observables (views), ordered by weakening.
--
-- Convention:
-- - `c ≤Ctx c'` means “c is weaker than c'”.
-- - So we have the weakening law: indistinguishable at `c'` ⇒ indistinguishable at `c`.
-- - Join (`⊔Ctx`) means “add observables”, hence yields a stronger context.

-- Large module split into:
-- - `ObsContext.OneD` : contexts as single views
-- - `ObsContext.TwoD` : contexts as `ShadowByView` packages

import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext.OneD as OneD
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext.TwoD as TwoD

open OneD public
open TwoD public
