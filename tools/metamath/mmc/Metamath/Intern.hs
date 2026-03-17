-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

module Metamath.Intern
  ( Interner
  , newInterner
  , intern
  , symbolsInOrder
  , numSymbols
  ) where

import Data.ByteString (ByteString)
import Data.IORef
import qualified Data.Map.Strict as Map

import Metamath.Types (Sym)

data Interner = Interner
  { symMap :: !(IORef (Map.Map ByteString Sym))
  , symListRev :: !(IORef [ByteString])
  , nextSym :: !(IORef Sym)
  }

newInterner :: IO Interner
newInterner = do
  m <- newIORef Map.empty
  xs <- newIORef []
  n <- newIORef 0
  pure Interner { symMap = m, symListRev = xs, nextSym = n }

intern :: Interner -> ByteString -> IO Sym
intern i tok = do
  mp <- readIORef (symMap i)
  case Map.lookup tok mp of
    Just k -> pure k
    Nothing -> do
      k <- readIORef (nextSym i)
      writeIORef (nextSym i) (k + 1)
      writeIORef (symMap i) (Map.insert tok k mp)
      modifyIORef' (symListRev i) (tok :)
      pure k

symbolsInOrder :: Interner -> IO [ByteString]
symbolsInOrder i = reverse <$> readIORef (symListRev i)

numSymbols :: Interner -> IO Sym
numSymbols i = readIORef (nextSym i)
