-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

module Metamath.Artifact
  ( ArtifactHeader(..)
  , headerSize
  , flagProofsChecked
  , writeHeaderPlaceholder
  , patchHeader
  , writeAssertionRecord
  , writeSymbolsSection
  , readHeader
  , readSymbolsAt
  , readAssertionRecord
  , readAssertionRecords
  ) where

import Control.Exception (throwIO)
import Control.Monad (unless, replicateM)
import Data.Binary.Get (getWord32le, getWord64le, runGet)
import qualified Data.ByteString as BS
import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as BB
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as LBS
import Data.Word (Word32, Word64)
import System.IO (Handle, hSeek, SeekMode (AbsoluteSeek))

import Metamath.Types (Expr, Label, MMError (..), Sym)

data ArtifactHeader = ArtifactHeader
  { ahVersion :: !Word32
  , ahFlags :: !Word32
  , ahOffsetSymbols :: !Word64
  , ahNumSymbols :: !Word32
  , ahNumAssertions :: !Word32
  } deriving (Show)

headerSize :: Integer
headerSize = 32

magic :: BS.ByteString
magic = BS8.pack "MMDB"

artifactVersion :: Word32
artifactVersion = 1

flagProofsChecked :: Word32
flagProofsChecked = 1

builderToStrict :: Builder -> BS.ByteString
builderToStrict = LBS.toStrict . BB.toLazyByteString

putU32 :: Word32 -> Builder
putU32 = BB.word32LE

putU64 :: Word64 -> Builder
putU64 = BB.word64LE

writeHeaderPlaceholder :: Handle -> Word32 -> IO ()
writeHeaderPlaceholder h flags = do
  let b =
        BB.byteString magic
          <> putU32 artifactVersion
          <> putU32 flags
          <> putU64 0 -- offsetSymbols placeholder
          <> putU32 0 -- numSymbols placeholder
          <> putU32 0 -- numAssertions placeholder
          <> putU32 0 -- reserved
  BS.hPut h (builderToStrict b)

patchHeader :: Handle -> ArtifactHeader -> IO ()
patchHeader h hdr = do
  -- We only patch the fields that are not known at write start.
  -- Offsets are fixed by the v1 header layout.
  hSeek h AbsoluteSeek 12
  BS.hPut h (builderToStrict (putU64 (ahOffsetSymbols hdr)))
  BS.hPut h (builderToStrict (putU32 (ahNumSymbols hdr)))
  BS.hPut h (builderToStrict (putU32 (ahNumAssertions hdr)))

writeByteStringLen :: BS.ByteString -> Builder
writeByteStringLen bs =
  putU32 (fromIntegral (BS.length bs)) <> BB.byteString bs

writeExpr :: Expr -> Builder
writeExpr xs =
  putU32 (fromIntegral (length xs))
    <> mconcat [putU32 (fromIntegral x) | x <- xs]

writeAssertionRecord :: Handle -> Label -> [Expr] -> Expr -> IO ()
writeAssertionRecord h label hyps concl = do
  let b =
        writeByteStringLen label
          <> putU32 (fromIntegral (length hyps))
          <> mconcat (map writeExpr hyps)
          <> writeExpr concl
  BS.hPut h (builderToStrict b)

writeSymbolsSection :: Handle -> [BS.ByteString] -> IO ()
writeSymbolsSection h syms = do
  let b =
        putU32 (fromIntegral (length syms))
          <> mconcat (map writeByteStringLen syms)
  BS.hPut h (builderToStrict b)

readExactly :: Handle -> Int -> IO BS.ByteString
readExactly h n = do
  bs <- BS.hGet h n
  unless (BS.length bs == n) $
    throwIO (MMError ("unexpected EOF while reading " <> show n <> " bytes"))
  pure bs

getU32IO :: Handle -> IO Word32
getU32IO h = do
  bs <- readExactly h 4
  pure (runGet getWord32le (LBS.fromStrict bs))

getU64IO :: Handle -> IO Word64
getU64IO h = do
  bs <- readExactly h 8
  pure (runGet getWord64le (LBS.fromStrict bs))

readHeader :: Handle -> IO ArtifactHeader
readHeader h = do
  m <- readExactly h 4
  unless (m == magic) $
    throwIO (MMError ("bad artifact magic (expected MMDB), got: " <> show m))
  ver <- getU32IO h
  unless (ver == artifactVersion) $
    throwIO (MMError ("unsupported artifact version: " <> show ver))
  fl <- getU32IO h
  offSyms <- getU64IO h
  nSyms <- getU32IO h
  nAsr <- getU32IO h
  _reserved <- getU32IO h
  pure $
    ArtifactHeader
      { ahVersion = ver
      , ahFlags = fl
      , ahOffsetSymbols = offSyms
      , ahNumSymbols = nSyms
      , ahNumAssertions = nAsr
      }

readLenBytesIO :: Handle -> IO BS.ByteString
readLenBytesIO h = do
  len <- getU32IO h
  readExactly h (fromIntegral len)

readExprIO :: Handle -> IO [Sym]
readExprIO h = do
  len <- getU32IO h
  ws <- replicateM (fromIntegral len) (getU32IO h)
  pure (map fromIntegral ws)

readAssertionRecord :: Handle -> IO (Label, [Expr], Expr)
readAssertionRecord h = do
  lbl <- readLenBytesIO h
  nh <- getU32IO h
  hyps <- replicateM (fromIntegral nh) (readExprIO h)
  concl <- readExprIO h
  pure (lbl, hyps, concl)

readAssertionRecords :: Handle -> Word32 -> IO [(Label, [Expr], Expr)]
readAssertionRecords h n = replicateM (fromIntegral n) (readAssertionRecord h)

readSymbolsAt :: Handle -> Word64 -> IO [BS.ByteString]
readSymbolsAt h off = do
  hSeek h AbsoluteSeek (fromIntegral off)
  n <- getU32IO h
  replicateM (fromIntegral n) (readLenBytesIO h)
