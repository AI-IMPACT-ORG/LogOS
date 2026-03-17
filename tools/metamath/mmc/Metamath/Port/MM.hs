-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

-- | Metamath statement stream (file ingest port).
--
-- This is intentionally a thin layer over 'Metamath.TokenStack': it turns the
-- token stream into the (small) statement algebra used by the compiler
-- transformer.
module Metamath.Port.MM
  ( Stmt(..)
  , ProofPolicy(..)
  , stmtStreamWith
  , nextStmt
  , nextStmtWith
  , readUntil
  , skipUntil
  ) where

import Control.Exception (throwIO)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8

import Metamath.Stream (Stream (..))
import Metamath.TokenStack (TokenStack, nextToken)
import Metamath.Types (Label, MMError (..))

data Stmt
  = StScopeOpen
  | StScopeClose
  | StConsts ![ByteString]
  | StVars ![ByteString]
  | StDisjoint ![ByteString]
  | StFloating !Label ![ByteString]
  | StEssential !Label ![ByteString]
  | StAxiom !Label ![ByteString]
  | StProvable !Label ![ByteString] ![Label]
  | StIgnore
  deriving (Show)

data ProofPolicy
  = KeepProofs
  | SkipProofs
  deriving (Show, Eq)

stmtStreamWith :: ProofPolicy -> TokenStack -> Stream Stmt
stmtStreamWith pol ts = Stream (nextStmtWith pol ts)

readUntil :: TokenStack -> ByteString -> IO [ByteString]
readUntil ts stop = go []
  where
    go acc = do
      mt <- nextToken ts
      case mt of
        Nothing -> throwIO (MMError ("unexpected EOF while scanning until " <> BS8.unpack stop))
        Just t ->
          if t == stop
            then pure (reverse acc)
            else go (t : acc)

skipUntil :: TokenStack -> ByteString -> IO ()
skipUntil ts stop = go
  where
    go = do
      mt <- nextToken ts
      case mt of
        Nothing -> throwIO (MMError ("unexpected EOF while skipping until " <> BS8.unpack stop))
        Just t ->
          if t == stop
            then pure ()
            else go

-- | Read one Metamath statement from the token stream.
--
-- This function consumes exactly the tokens for one statement and returns its
-- payload.  Non-semantic $t/$j blocks are skipped as 'StIgnore'.
nextStmt :: TokenStack -> IO (Maybe Stmt)
nextStmt = nextStmtWith KeepProofs

nextStmtWith :: ProofPolicy -> TokenStack -> IO (Maybe Stmt)
nextStmtWith pol ts = do
  mtok <- nextToken ts
  case mtok of
    Nothing -> pure Nothing
    Just tok
      | tok == BS8.pack "${" -> pure (Just StScopeOpen)
      | tok == BS8.pack "$}" -> pure (Just StScopeClose)
      | tok == BS8.pack "$c" -> Just . StConsts <$> readUntil ts (BS8.pack "$.")
      | tok == BS8.pack "$v" -> Just . StVars <$> readUntil ts (BS8.pack "$.")
      | tok == BS8.pack "$d" -> Just . StDisjoint <$> readUntil ts (BS8.pack "$.")
      | tok == BS8.pack "$t" || tok == BS8.pack "$j" -> do
          _ <- readUntil ts (BS8.pack "$.")
          pure (Just StIgnore)
      | otherwise -> do
          let label = tok
          mstype <- nextToken ts
          stype <- case mstype of
            Nothing -> throwIO (MMError ("unexpected EOF after label " <> BS8.unpack label))
            Just x -> pure x
          case stype of
            t | t == BS8.pack "$f" -> do
                body <- readUntil ts (BS8.pack "$.")
                pure (Just (StFloating label body))
            t | t == BS8.pack "$e" -> do
                body <- readUntil ts (BS8.pack "$.")
                pure (Just (StEssential label body))
            t | t == BS8.pack "$a" -> do
                body <- readUntil ts (BS8.pack "$.")
                pure (Just (StAxiom label body))
            t | t == BS8.pack "$p" -> do
                exprToks <- readUntil ts (BS8.pack "$=")
                proofToks <-
                  case pol of
                    KeepProofs -> readUntil ts (BS8.pack "$.")
                    SkipProofs -> skipUntil ts (BS8.pack "$.") >> pure []
                pure (Just (StProvable label exprToks proofToks))
            _ ->
              throwIO
                (MMError ("unknown statement type after " <> BS8.unpack label <> ": " <> BS8.unpack stype))
