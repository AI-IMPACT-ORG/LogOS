{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Bridges where

-- Canonical bridge surface: relation-safe connectors between core layers.
--
-- This surface is for:
-- - tier alignment (S/H/G/R) and tier-categorical views,
-- - kernel shape bridges (graded/ungraded -> kernel),
-- - flow/endomap bridges (hom + endo + sub-2-category wrappers),
-- - process-limit bridges (`run∞` + continuity-marked morphisms).
--
-- This module keeps existing APIs intact and exposes only already-defined
-- bridge constructs in one place.

-- Export style:
-- - no broad prelude/kernels re-export at top-level;
-- - explicit bridge namespaces avoid accidental ambiguity downstream.

module Repr where
  import LogOS.Kernel.FromUngradedKernel as Ungradedₐ
  import LogOS.Kernel.FromGradedKernel as Gradedₐ

  module Ungraded = Ungradedₐ
  module Graded = Gradedₐ

  asKernelUngraded = Ungradedₐ.asKernel
  asKernelGraded = Gradedₐ.asKernel

module Tier where
  import LogOS.Kernel.Tiers as Tiersₐ
  import LogOS.Kernel.TierCategorical as TierCategoricalₐ

  module Tiers = Tiersₐ
  module Categorical = TierCategoricalₐ

module Flow where
  import LogOS.Kernel.Endo as Endoₐ
  import LogOS.Kernel.Hom as Homₐ
  import LogOS.Kernel.Hom2Cat as Hom2Catₐ
  import LogOS.Kernel.Hom2Cat.FlowSub2Cat as FlowSub2Catₐ
  import LogOS.Kernel.UngradedKernel.EndoCore as UngradedEndoCoreₐ
  import LogOS.Kernel.UngradedKernel.EndoRelative as UngradedEndoRelativeₐ

  module Endo = Endoₐ
  module Hom = Homₐ
  module Hom2Cat = Hom2Catₐ
  module FlowSub2Cat = FlowSub2Catₐ
  module UngradedEndoCore = UngradedEndoCoreₐ
  module UngradedEndoRelative = UngradedEndoRelativeₐ

module Limit where
  import LogOS.Computation.ProcessLimit as Processₐ
  import LogOS.Computation.ProcessLimitSub2Cat as Sub2Catₐ

  module Process = Processₐ
  module Sub2Cat = Sub2Catₐ
