-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Control.Exception (catch)
import Control.Monad (when)
import qualified System.Environment
import System.Exit (exitFailure)
import System.FilePath ((</>), takeBaseName, takeDirectory)
import System.IO (IOMode (ReadMode), hClose, hPutStrLn, openBinaryFile, stderr)

import Metamath.Artifact (ArtifactHeader (..), readHeader)
import Metamath.Compile (CompileOptions (..), compileMMDB)
import Metamath.EmitAgda (ExportAgdaOptions (..), exportAgda)
import Metamath.EmitAgdaRuntime (ExportAgdaRuntimeOptions (..), exportAgdaRuntime)
import Metamath.Types (MMError (..))

main :: IO ()
main = do
  args <- getArgsCompat
  case args of
    ("compile" : root : rest) ->
      runCompile root rest `catch` onMMError
    ("export-agda" : artDir : rest) ->
      runExportAgda artDir rest `catch` onMMError
    ("export-agda-runtime" : artDir : rest) ->
      runExportAgdaRuntime artDir rest `catch` onMMError
    _ -> do
      hPutStrLn stderr usage
      exitFailure
  where
    onMMError :: MMError -> IO ()
    onMMError (MMError msg) = do
      hPutStrLn stderr ("mmc: ERROR: " <> msg)
      exitFailure

usage :: String
usage =
  unlines
    [ "mmc: Metamath compiler (LogOS port ingest)"
    , ""
    , "Commands:"
    , "  mmc compile ROOT.mm --out DIR [--check-proofs] [--max-assertions N] [--progress-every N]"
    , "  mmc export-agda ARTIFACT_DIR --emit-agda OUT.agda --agda-module Mod.Name [--chunk-size N] [--max-assertions N]"
    , "  mmc export-agda-runtime ARTIFACT_DIR --emit-agda OUT.agda --agda-module Mod.Name [--env-var NAME] [--emit-runner OUT.agda] [--runner-module Mod.Name]"
    , ""
    , "Notes:"
    , "  export-agda-runtime also emits a host FFI module:"
    , "    OUT_DIR/OUT_BASE/Host.agda  (module Mod.Name.Host)"
    ]

runCompile :: FilePath -> [String] -> IO ()
runCompile root rest = do
  opts <- parseCompile root rest
  compileMMDB opts
  let dbPath = optOutDir opts </> "db.mmdb"
  h <- openBinaryFile dbPath ReadMode
  hdr <- readHeader h
  hClose h
  putStrLn ("Wrote: " <> dbPath)
  putStrLn ("  symbols: " <> show (ahNumSymbols hdr) <> ", assertions: " <> show (ahNumAssertions hdr))
  putStrLn ("Wrote: " <> optOutDir opts </> "manifest.json")

parseCompile :: FilePath -> [String] -> IO CompileOptions
parseCompile root = go opts0
  where
    opts0 =
      CompileOptions
        { optRootMM = root
        , optOutDir = ""
        , optCheckProofs = False
        , optMaxAssertions = Nothing
        , optProgressEvery = Nothing
        }

    go opts = \case
      [] -> do
        when (null (optOutDir opts)) $
          failUsage "compile: missing required --out DIR"
        pure opts
      "--out" : dir : xs ->
        go (opts { optOutDir = dir }) xs
      "--check-proofs" : xs ->
        go (opts { optCheckProofs = True }) xs
      "--max-assertions" : n : xs ->
        readNat "compile --max-assertions" n >>= \k ->
          go (opts { optMaxAssertions = Just k }) xs
      "--progress-every" : n : xs ->
        readNat "compile --progress-every" n >>= \k ->
          go (opts { optProgressEvery = Just k }) xs
      "--help" : _ ->
        failUsage usage
      x : _ ->
        failUsage ("compile: unknown option: " <> x)

runExportAgda :: FilePath -> [String] -> IO ()
runExportAgda artDir rest = do
  opts <- parseExportAgda artDir rest
  exportAgda opts
  putStrLn ("Wrote: " <> eoEmitAgdaPath opts)

parseExportAgda :: FilePath -> [String] -> IO ExportAgdaOptions
parseExportAgda artDir = go opts0
  where
    opts0 =
      ExportAgdaOptions
        { eoArtifactDir = artDir
        , eoEmitAgdaPath = ""
        , eoAgdaModule = ""
        , eoChunkSize = Nothing
        , eoMaxAssertions = Nothing
        }

    go opts = \case
      [] -> do
        when (null (eoEmitAgdaPath opts)) $
          failUsage "export-agda: missing required --emit-agda OUT.agda"
        when (null (eoAgdaModule opts)) $
          failUsage "export-agda: missing required --agda-module Mod.Name"
        pure opts
      "--emit-agda" : p : xs ->
        go (opts { eoEmitAgdaPath = p }) xs
      "--agda-module" : m : xs ->
        go (opts { eoAgdaModule = m }) xs
      "--chunk-size" : n : xs ->
        readNat "export-agda --chunk-size" n >>= \k ->
          go (opts { eoChunkSize = Just k }) xs
      "--max-assertions" : n : xs ->
        readNat "export-agda --max-assertions" n >>= \k ->
          go (opts { eoMaxAssertions = Just k }) xs
      "--help" : _ ->
        failUsage usage
      x : _ ->
        failUsage ("export-agda: unknown option: " <> x)

runExportAgdaRuntime :: FilePath -> [String] -> IO ()
runExportAgdaRuntime artDir rest = do
  opts <- parseExportAgdaRuntime artDir rest
  exportAgdaRuntime opts
  putStrLn ("Wrote: " <> roEmitAgdaPath opts)
  let outPath = roEmitAgdaPath opts
      hostPath = takeDirectory outPath </> takeBaseName outPath </> "Host.agda"
  putStrLn ("Wrote: " <> hostPath)
  case roEmitRunnerPath opts of
    Nothing -> pure ()
    Just p -> putStrLn ("Wrote: " <> p)

parseExportAgdaRuntime :: FilePath -> [String] -> IO ExportAgdaRuntimeOptions
parseExportAgdaRuntime artDir = go opts0
  where
    opts0 =
      ExportAgdaRuntimeOptions
        { roArtifactDir = artDir
        , roEmitAgdaPath = ""
        , roAgdaModule = ""
        , roEnvVar = "MMDB_PATH"
        , roEmitRunnerPath = Nothing
        , roRunnerModule = Nothing
        }

    go opts = \case
      [] -> do
        when (null (roEmitAgdaPath opts)) $
          failUsage "export-agda-runtime: missing required --emit-agda OUT.agda"
        when (null (roAgdaModule opts)) $
          failUsage "export-agda-runtime: missing required --agda-module Mod.Name"
        pure opts
      "--emit-agda" : p : xs ->
        go (opts { roEmitAgdaPath = p }) xs
      "--agda-module" : m : xs ->
        go (opts { roAgdaModule = m }) xs
      "--env-var" : v : xs ->
        go (opts { roEnvVar = v }) xs
      "--emit-runner" : p : xs ->
        go (opts { roEmitRunnerPath = Just p }) xs
      "--runner-module" : m : xs ->
        go (opts { roRunnerModule = Just m }) xs
      "--help" : _ ->
        failUsage usage
      x : _ ->
        failUsage ("export-agda-runtime: unknown option: " <> x)

failUsage :: String -> IO a
failUsage msg = do
  hPutStrLn stderr msg
  hPutStrLn stderr ""
  hPutStrLn stderr usage
  exitFailure

readNat :: String -> String -> IO Int
readNat ctx s =
  case reads s of
    [(n, "")] ->
      if n > 0
        then pure n
        else failUsage (ctx <> ": expected a positive integer, got " <> show n)
    _ -> failUsage (ctx <> ": expected an integer, got " <> show s)

getArgsCompat :: IO [String]
getArgsCompat = do
  System.Environment.getArgs
