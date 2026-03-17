-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE LambdaCase #-}

-- | Small statement normalisations (stream transformer).
module Metamath.Transform.Normalize
  ( dropIgnored
  ) where

import Metamath.Port.MM (Stmt (..))
import Metamath.Stream (Stream, mapMaybe)

-- | Drop non-semantic statements ($t/$j blocks etc).
dropIgnored :: Stream Stmt -> Stream Stmt
dropIgnored =
  mapMaybe $ \case
    StIgnore -> pure Nothing
    st -> pure (Just st)

