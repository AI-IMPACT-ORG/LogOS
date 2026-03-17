-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

module Metamath.Types
  ( MMError(..)
  , Label
  , Sym
  , Expr
  , FloatingHyp(..)
  , EssentialHyp(..)
  , Assertion(..)
  ) where

import Control.Exception (Exception)
import Data.ByteString (ByteString)

newtype MMError = MMError { unMMError :: String }
  deriving (Show)

instance Exception MMError

type Label = ByteString

-- Interned symbol index (0-based).
type Sym = Int

-- A Metamath "math string" as a flat list of interned symbol indices.
-- Invariant: non-empty, with a typecode (a constant) in head position.
type Expr = [Sym]

data FloatingHyp = FloatingHyp
  { fhLabel :: !Label
  , fhTypecode :: !Sym
  , fhVar :: !Sym
  } deriving (Show)

data EssentialHyp = EssentialHyp
  { ehLabel :: !Label
  , ehExpr :: !Expr
  } deriving (Show)

data Assertion = Assertion
  { asLabel :: !Label
  , asExpr :: !Expr
  , asFloatHyps :: ![Label] -- mandatory $f labels, in order
  , asEssHyps :: ![Label]   -- mandatory $e labels, in order
  , asDvPairs :: ![(Sym, Sym)] -- (x,y) with x < y, mandatory vars only
  } deriving (Show)
