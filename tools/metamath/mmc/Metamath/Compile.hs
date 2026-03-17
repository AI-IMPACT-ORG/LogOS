-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

module Metamath.Compile
  ( CompileOptions(..)
  , compileMMDB
  ) where

import Control.Exception (bracket, throwIO)
import Control.Monad (when)
import Data.Bits ((.&.))
import qualified Data.List as List
import Data.Time.Clock (getCurrentTime)
import Data.Time.Format (defaultTimeLocale, formatTime)
import System.Directory (createDirectoryIfMissing, canonicalizePath)
import System.FilePath ((</>))
import System.IO
  ( IOMode (WriteMode)
  , hClose
  , hTell
  , openBinaryFile
  )

import Metamath.Artifact
  ( ArtifactHeader (..)
  , flagProofsChecked
  , patchHeader
  , writeHeaderPlaceholder
  , writeSymbolsSection
  )
import Metamath.Intern (newInterner, symbolsInOrder)
import Metamath.Port.MM (ProofPolicy (..), stmtStreamWith)
import Metamath.TokenStack (inComment, openedFiles, withTokenStack)
import Metamath.Transform.Compile (CompileConfig (..), St (..), compileStream, st0)
import Metamath.Transform.Normalize (dropIgnored)
import Metamath.Types (MMError (..))

data CompileOptions = CompileOptions
  { optRootMM :: !FilePath
  , optOutDir :: !FilePath
  , optCheckProofs :: !Bool
  , optMaxAssertions :: !(Maybe Int)
  , optProgressEvery :: !(Maybe Int)
  }

compileMMDB :: CompileOptions -> IO ()
compileMMDB opts = do
  outDir <- canonicalizePath (optOutDir opts)
  createDirectoryIfMissing True outDir

  rootResolved <- canonicalizePath (optRootMM opts)

  let dbPath = outDir </> "db.mmdb"
      manifestPath = outDir </> "manifest.json"
      flags = if optCheckProofs opts then flagProofsChecked else 0

  interner <- newInterner

  bracket (openBinaryFile dbPath WriteMode) hClose $ \hDb -> do
    writeHeaderPlaceholder hDb flags

    (stFinal, files) <-
      withTokenStack rootResolved $ \ts -> do
        let cfg =
              CompileConfig
                { ccCheckProofs = optCheckProofs opts
                , ccMaxAssertions = optMaxAssertions opts
                , ccProgressEvery = optProgressEvery opts
                }
            pol = if ccCheckProofs cfg then KeepProofs else SkipProofs
            stmts = dropIgnored (stmtStreamWith pol ts)
        st <- compileStream stmts interner hDb cfg st0
        files <- openedFiles ts
        cm <- inComment ts
        when cm $
          throwIO (MMError "unclosed comment at EOF (missing $))")
        pure (st, files)

    syms <- symbolsInOrder interner
    offSyms <- hTell hDb
    writeSymbolsSection hDb syms

    let hdr =
          ArtifactHeader
            { ahVersion = 1
            , ahFlags = flags
            , ahOffsetSymbols = fromIntegral offSyms
            , ahNumSymbols = fromIntegral (length syms)
            , ahNumAssertions = fromIntegral (stCount stFinal)
            }
    patchHeader hDb hdr

    writeManifest manifestPath rootResolved files hdr stFinal

writeManifest :: FilePath -> FilePath -> [FilePath] -> ArtifactHeader -> St -> IO ()
writeManifest outPath root files hdr st = do
  now <- getCurrentTime
  let ts = formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%SZ" now
      json =
        unlines
          [ "{"
          , "  \"artifact_version\": 1,"
          , "  \"created_at\": " <> jstr ts <> ","
          , "  \"mm_root\": " <> jstr root <> ","
          , "  \"includes\": " <> jarr (map jstr files) <> ","
          , "  \"proofs_checked\": " <> jbool ((ahFlags hdr .&. flagProofsChecked) /= 0) <> ","
          , "  \"num_symbols\": " <> show (ahNumSymbols hdr) <> ","
          , "  \"num_assertions\": " <> show (ahNumAssertions hdr) <> ","
          , "  \"num_a\": " <> show (stCountA st) <> ","
          , "  \"num_p\": " <> show (stCountP st)
          , "}"
          ]
  writeFile outPath json
  where
    jstr s = "\"" <> escape s <> "\""
    jbool True = "true"
    jbool False = "false"
    jarr xs = "[" <> List.intercalate ", " xs <> "]"
    escape = concatMap esc
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\r' = "\\r"
    esc '\t' = "\\t"
    esc c = [c]
