-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

module Metamath.EmitAgda
  ( ExportAgdaOptions(..)
  , exportAgda
  ) where

import Control.Exception (bracket, throwIO)
import Control.Monad (forM, forM_, when)
import Data.ByteString (ByteString)
import Data.Word (Word32)
import System.Directory (createDirectoryIfMissing)
import System.FilePath
  ( takeBaseName
  , takeDirectory
  , takeExtension
  , (</>)
  )
import System.IO (Handle, IOMode (ReadMode), hClose, openBinaryFile)
import System.IO (SeekMode (AbsoluteSeek), hSeek)

import Metamath.Artifact
  ( ArtifactHeader (..)
  , headerSize
  , readAssertionRecord
  , readHeader
  , readSymbolsAt
  )
import Metamath.Emit.Common
import Metamath.Types (Expr, Label, MMError (..))
import Metamath.SetMMSig (setMMSigBlock)


data ExportAgdaOptions = ExportAgdaOptions
  { eoArtifactDir :: !FilePath
  , eoEmitAgdaPath :: !FilePath
  , eoAgdaModule :: !String
  , eoChunkSize :: !(Maybe Int)
  , eoMaxAssertions :: !(Maybe Int)
  }

exportAgda :: ExportAgdaOptions -> IO ()
exportAgda opts = do
  -- Create the parent dir; chunked mode will also create the sibling chunk dir.
  createDirectoryIfMissing True (takeDirectory (eoEmitAgdaPath opts))
  when (takeExtension (eoEmitAgdaPath opts) /= ".agda") $
    throwIO (MMError ("--emit-agda must be a .agda file, got: " <> eoEmitAgdaPath opts))

  let dbPath = eoArtifactDir opts </> "db.mmdb"

  bracket (openBinaryFile dbPath ReadMode) hClose $ \h -> do
    hdr <- readHeader h
    syms <- readSymbolsAt h (ahOffsetSymbols hdr)
    -- `readSymbolsAt` seeks the handle; rewind to the assertion section.
    hSeek h AbsoluteSeek (fromIntegral headerSize)
    let total = fromIntegral (ahNumAssertions hdr) :: Int
        n = clampMax (eoMaxAssertions opts) total
    case eoChunkSize opts of
      Nothing -> emitOne hdr syms n h
      Just k -> emitChunks hdr syms n k h
  where
    clampMax :: Maybe Int -> Int -> Int
    clampMax Nothing total = total
    clampMax (Just mx) total
      | mx <= 0 = total
      | otherwise = min mx total

    emitOne :: ArtifactHeader -> [ByteString] -> Int -> Handle -> IO ()
    emitOne hdr syms n h = do
      recs <- forM [1 .. n] $ \_ -> readAssertionRecord h
      let labels = map (\(l, _, _) -> l) recs
          premisesRows = map (\(_, hyps, _) -> hyps) recs
          conclRows = map (\(_, _, c) -> c) recs
      writeAgdaModule
        (eoEmitAgdaPath opts)
        (eoAgdaModule opts)
        (fromIntegral (ahNumSymbols hdr))
        n
        syms
        labels
        premisesRows
        conclRows

    emitChunks :: ArtifactHeader -> [ByteString] -> Int -> Int -> Handle -> IO ()
    emitChunks hdr syms n chunkSize0 h = do
      when (chunkSize0 <= 0) $
        throwIO (MMError ("--chunk-size must be positive, got: " <> show chunkSize0))

      let outAgg = eoEmitAgdaPath opts
          outDir = takeDirectory outAgg
          chunkDir = outDir </> takeBaseName outAgg

      createDirectoryIfMissing True chunkDir

      let numChunks = (n + chunkSize0 - 1) `div` chunkSize0

      -- Emit chunk modules.
      forM_ [0 .. numChunks - 1] $ \ci -> do
        let remaining = n - ci * chunkSize0
            k = min chunkSize0 remaining
        recs <- forM [1 .. k] $ \_ -> readAssertionRecord h
        let labels = map (\(l, _, _) -> l) recs
            premisesRows = map (\(_, hyps, _) -> hyps) recs
            conclRows = map (\(_, _, c) -> c) recs
            chunkMod = eoAgdaModule opts <> ".Chunk" <> pad4 ci
            chunkPath = chunkDir </> ("Chunk" <> pad4 ci <> ".agda")
            globalStart = ci * chunkSize0
        writeAgdaChunk
          chunkPath
          chunkMod
          globalStart
          labels
          premisesRows
          conclRows

      -- Emit aggregator module.
      writeAgdaAggregator
        outAgg
        (eoAgdaModule opts)
        (fromIntegral (ahNumSymbols hdr))
        n
        chunkSize0
        numChunks
        syms

-- Emit a single safe module DB with Label = Nat (assertion index).
writeAgdaModule
  :: FilePath
  -> String
  -> Word32
  -> Int
  -> [ByteString]
  -> [Label]
  -> [[Expr]]
  -> [Expr]
  -> IO ()
writeAgdaModule outPath moduleName numSyms numAsr syms labels premisesRows conclRows = do
  let docLines =
        agdaModuleHeader moduleName True
        <> agdaKernelPrelude
        <> [ "import LogOS.Ports.Metamath as MM"
        , ""
        ]
        <> agdaFormulaTypeDecl
        <> [ "numSymbols : ℕ"
        , "numSymbols = " <> show numSyms
        , ""
        , "numAssertions : ℕ"
        , "numAssertions = " <> show numAsr
        ]
          <> setMMSigBlock syms
          <> [ ""
        , ""
        , "-- Symbol table (index -> original token)."
        ]
          <> symbolIndexComments syms
          <> [ ""
             , "-- Assertion index -> original Metamath label."
             ]
          <> symbolIndexComments labels
          <> [ ""
             , "premisesTable : List (List Formula)"
             , "premisesTable = " <> agdaListListFormula (map (map (map fromIntegral)) premisesRows)
             , ""
             , "conclTable : List Formula"
             , "conclTable = " <> agdaListFormula (map (map fromIntegral) conclRows)
             , ""
             , "lookup : ∀ {A : Set} → ℕ → List A → A → A"
             , "lookup zero (x ∷ xs) d = x"
             , "lookup (suc n) (x ∷ xs) d = lookup n xs d"
             , "lookup _ [] d = d"
             , ""
             , "hyps : ℕ → List Formula"
             , "hyps n = lookup n premisesTable []"
             , ""
             , "concl : ℕ → Formula"
             , "concl n = lookup n conclTable []"
             , ""
             , "DB : MM.Database Formula"
             , "DB = record { Label = ℕ ; hyps = hyps ; concl = concl }"
             , ""
             , "-- Derived: closure transformer for this database."
             , "module Closed = MM.FromDB DB"
             , ""
             ]
  writeFile outPath (unlines docLines)

-- Emit one chunk module (no DB record here; aggregator wires them together).
writeAgdaChunk
  :: FilePath
  -> String
  -> Int
  -> [Label]
  -> [[Expr]]
  -> [Expr]
  -> IO ()
writeAgdaChunk outPath moduleName globalStart labels premisesRows conclRows = do
  let docLines =
        agdaModuleHeader moduleName True
        <> agdaKernelPrelude
        <> agdaFormulaTypeDecl
        <> [ "-- Local assertion index -> original Metamath label."
           , "-- Global start index: " <> show globalStart
           ]
          <> symbolIndexComments labels
          <> [ ""
             , "premisesTable : List (List Formula)"
             , "premisesTable = " <> agdaListListFormula (map (map (map fromIntegral)) premisesRows)
             , ""
             , "conclTable : List Formula"
             , "conclTable = " <> agdaListFormula (map (map fromIntegral) conclRows)
             , ""
             , "lookup : ∀ {A : Set} → ℕ → List A → A → A"
             , "lookup zero (x ∷ xs) d = x"
             , "lookup (suc n) (x ∷ xs) d = lookup n xs d"
             , "lookup _ [] d = d"
             , ""
             , "hypsL : ℕ → List Formula"
             , "hypsL n = lookup n premisesTable []"
             , ""
             , "conclL : ℕ → Formula"
             , "conclL n = lookup n conclTable []"
             , ""
             ]
  writeFile outPath (unlines docLines)

-- Emit the aggregator module that stitches the chunks into a single `MM.Database`.
writeAgdaAggregator
  :: FilePath
  -> String
  -> Word32
  -> Int
  -> Int
  -> Int
  -> [ByteString]
  -> IO ()
writeAgdaAggregator outPath moduleName numSyms numAsr chunkSize0 numChunks syms = do
  let docLines =
        agdaModuleHeader moduleName True
        <> agdaKernelPrelude
        <> [ "import LogOS.Ports.Metamath as MM"
        , ""
        ]
        <> agdaFormulaTypeDecl
        <> [ "numSymbols : ℕ"
        , "numSymbols = " <> show numSyms
        , ""
        , "numAssertions : ℕ"
        , "numAssertions = " <> show numAsr
        ]
          <> setMMSigBlock syms
          <> [ ""
        , ""
        , "chunkSize : ℕ"
        , "chunkSize = " <> show chunkSize0
        , ""
        , "numChunks : ℕ"
        , "numChunks = " <> show numChunks
        , ""
        , "-- Assertions: " <> show numAsr <> " (chunk size " <> show chunkSize0 <> ", chunks " <> show numChunks <> ")"
        , ""
        , "-- Symbol table (index -> original token)."
        ]
          <> symbolIndexComments syms
          <> [ "" ]
          <> [ "import " <> moduleName <> ".Chunk" <> pad4 ci <> " as C" <> pad4 ci | ci <- [0 .. numChunks - 1] ]
          <> [ ""
             , "-- Labels are (chunk-index, local-index)."
             , "Label : Set"
             , "Label = ℕ × ℕ"
             , ""
             , "hyps : Label → List Formula"
             ]
          <> [ "hyps (" <> agdaNatPat ci <> " , n) = C" <> pad4 ci <> ".hypsL n" | ci <- [0 .. numChunks - 1] ]
          <> [ "hyps (_ , _) = []"
             , ""
             , "concl : Label → Formula"
             ]
          <> [ "concl (" <> agdaNatPat ci <> " , n) = C" <> pad4 ci <> ".conclL n" | ci <- [0 .. numChunks - 1] ]
          <> [ "concl (_ , _) = []"
             , ""
             , "DB : MM.Database Formula"
             , "DB = record { Label = Label ; hyps = hyps ; concl = concl }"
             , ""
             , "-- Derived: closure transformer for this database."
             , "module Closed = MM.FromDB DB"
             , ""
             ]
  writeFile outPath (unlines docLines)
