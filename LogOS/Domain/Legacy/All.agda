{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Legacy.All where

-- Legacy-only aggregation surface. Not used by curated packs.

module Complexity where
  open import LogOS.Domain.Legacy.Complexity.PvsNP public

module Opacity where
  open import LogOS.Domain.Legacy.Opacity.AccessibleWeilLimitBridge public
  open import LogOS.Domain.Legacy.Opacity.AccessibleWeilMeetLimitBridge public
  open import LogOS.Domain.Legacy.Opacity.ZetaAccessibleMeetLimitLedger public
