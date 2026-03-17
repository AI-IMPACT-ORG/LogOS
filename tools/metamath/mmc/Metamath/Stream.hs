-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

-- | Minimal pull-based stream abstraction for the mmc transformer stack.
module Metamath.Stream
  ( Stream(..)
  , mapMaybe
  , filterStream
  ) where

newtype Stream a = Stream { pull :: IO (Maybe a) }

-- | Transform a stream, with the option to drop elements ('Nothing').
--
-- NOTE: returning 'Nothing' drops the element and continues; end-of-stream is
-- driven only by the upstream 'pull' returning 'Nothing'.
mapMaybe :: (a -> IO (Maybe b)) -> Stream a -> Stream b
mapMaybe f (Stream pullA) = Stream go
  where
    go = do
      ma <- pullA
      case ma of
        Nothing -> pure Nothing
        Just a -> do
          mb <- f a
          case mb of
            Nothing -> go
            Just b -> pure (Just b)

filterStream :: (a -> Bool) -> Stream a -> Stream a
filterStream p =
  mapMaybe (\a -> pure (if p a then Just a else Nothing))

