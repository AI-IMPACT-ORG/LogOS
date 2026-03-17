-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

module Metamath.TokenStack
  ( TokenStack
  , withTokenStack
  , nextToken
  , openedFiles
  , inComment
  ) where

import Control.Exception (bracket, throwIO)
import Control.Monad (unless, when)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Set as Set
import Data.IORef
import System.Directory (canonicalizePath, doesFileExist)
import System.FilePath (takeDirectory, (</>))
import System.IO (Handle, IOMode (ReadMode), hClose, hIsEOF, openFile)

import Metamath.Types (MMError (..))

data TokenSource = TokenSource
  { srcPath :: !FilePath
  , srcHandle :: !Handle
  , srcBuf :: !(IORef [ByteString])
  }

data TokenStack = TokenStack
  { tsStack :: !(IORef [TokenSource])
  , tsIncludeChain :: !(IORef [FilePath]) -- resolved, top is most recent
  , tsOpenedRev :: !(IORef [FilePath])    -- resolved, unique, reverse chronological
  , tsOpenedSet :: !(IORef (Set.Set FilePath))
  , tsInComment :: !(IORef Bool)
  }

withTokenStack :: FilePath -> (TokenStack -> IO a) -> IO a
withTokenStack root =
  bracket (newTokenStack root) closeTokenStack

newTokenStack :: FilePath -> IO TokenStack
newTokenStack root = do
  rootResolved <- canonicalizePath root
  exists <- doesFileExist rootResolved
  unless exists $
    throwIO (MMError ("root .mm file not found: " <> rootResolved))

  h <- openFile rootResolved ReadMode
  bufRef <- newIORef []
  let src = TokenSource { srcPath = rootResolved, srcHandle = h, srcBuf = bufRef }

  stRef <- newIORef [src]
  chainRef <- newIORef [rootResolved]
  openedRevRef <- newIORef [rootResolved]
  openedSetRef <- newIORef (Set.singleton rootResolved)
  inCommentRef <- newIORef False

  pure $
    TokenStack
      { tsStack = stRef
      , tsIncludeChain = chainRef
      , tsOpenedRev = openedRevRef
      , tsOpenedSet = openedSetRef
      , tsInComment = inCommentRef
      }

closeTokenStack :: TokenStack -> IO ()
closeTokenStack ts = do
  srcs <- readIORef (tsStack ts)
  mapM_ (hClose . srcHandle) srcs
  writeIORef (tsStack ts) []
  writeIORef (tsIncludeChain ts) []

openedFiles :: TokenStack -> IO [FilePath]
openedFiles ts = reverse <$> readIORef (tsOpenedRev ts)

inComment :: TokenStack -> IO Bool
inComment ts = readIORef (tsInComment ts)

-- Read the next raw whitespace token from the current file stack.
nextTok0 :: TokenStack -> IO (Maybe ByteString)
nextTok0 ts = do
  srcs <- readIORef (tsStack ts)
  case srcs of
    [] -> pure Nothing
    (src : rest) -> do
      mtok <- nextRawToken src
      case mtok of
        Just tok -> pure (Just tok)
        Nothing -> do
          -- EOF: pop this source.
          hClose (srcHandle src)
          writeIORef (tsStack ts) rest
          -- Maintain include chain.
          chain <- readIORef (tsIncludeChain ts)
          case chain of
            [] -> pure ()
            (_ : chainRest) -> writeIORef (tsIncludeChain ts) chainRest
          nextTok0 ts

-- Per-file raw token stream (no comments/includes).
nextRawToken :: TokenSource -> IO (Maybe ByteString)
nextRawToken src = do
  buf <- readIORef (srcBuf src)
  case buf of
    (t : ts) -> writeIORef (srcBuf src) ts >> pure (Just t)
    [] -> do
      eof <- hIsEOF (srcHandle src)
      if eof
        then pure Nothing
        else do
          line <- BS8.hGetLine (srcHandle src)
          let toks = BS8.words line
          writeIORef (srcBuf src) toks
          nextRawToken src

-- Next token, with comment stripping and include processing.
nextToken :: TokenStack -> IO (Maybe ByteString)
nextToken ts = loop
  where
    loop = do
      mtok <- nextTok0 ts
      case mtok of
        Nothing -> pure Nothing
        Just tok -> do
          c <- readIORef (tsInComment ts)
          if c
            then do
              when (tok == BS8.pack "$)") $ writeIORef (tsInComment ts) False
              loop
            else
              if tok == BS8.pack "$("
                then writeIORef (tsInComment ts) True >> loop
                else
                  if tok == BS8.pack "$["
                    then do
                      mfname <- nextTokenNoInclude ts
                      fname <- case mfname of
                        Nothing -> throwIO (MMError "unexpected EOF after $[")
                        Just x -> pure x
                      mclose <- nextTokenNoInclude ts
                      close <- case mclose of
                        Nothing -> throwIO (MMError "unexpected EOF in include (missing $])")
                        Just x -> pure x
                      unless (close == BS8.pack "$]") $
                        throwIO (MMError ("malformed include: expected $], got " <> BS8.unpack close))
                      pushInclude ts (BS8.unpack fname)
                      loop
                    else pure (Just tok)

-- Next token for include-argument scanning: strips comments, but does not allow nested includes.
nextTokenNoInclude :: TokenStack -> IO (Maybe ByteString)
nextTokenNoInclude ts = loop
  where
    loop = do
      mtok <- nextTok0 ts
      case mtok of
        Nothing -> pure Nothing
        Just tok -> do
          c <- readIORef (tsInComment ts)
          if c
            then do
              when (tok == BS8.pack "$)") $ writeIORef (tsInComment ts) False
              loop
            else
              if tok == BS8.pack "$("
                then writeIORef (tsInComment ts) True >> loop
                else
                  if tok == BS8.pack "$["
                    then throwIO (MMError "nested $[ include inside include header")
                    else pure (Just tok)

pushInclude :: TokenStack -> FilePath -> IO ()
pushInclude ts fname = do
  srcs <- readIORef (tsStack ts)
  cur <- case srcs of
    [] -> throwIO (MMError "internal: include with empty token stack")
    (src : _) -> pure src

  let incPath0 = takeDirectory (srcPath cur) </> fname
  incPath <- canonicalizePath incPath0

  exists <- doesFileExist incPath
  unless exists $
    throwIO (MMError ("included file not found: " <> incPath))

  chain <- readIORef (tsIncludeChain ts)
  when (incPath `elem` chain) $ do
    let chainStr = unwords (reverse (incPath : chain))
    throwIO (MMError ("include cycle detected: " <> chainStr))

  h <- openFile incPath ReadMode
  bufRef <- newIORef []
  let src = TokenSource { srcPath = incPath, srcHandle = h, srcBuf = bufRef }

  writeIORef (tsStack ts) (src : srcs)
  writeIORef (tsIncludeChain ts) (incPath : chain)

  openedSet <- readIORef (tsOpenedSet ts)
  unless (Set.member incPath openedSet) $ do
    writeIORef (tsOpenedSet ts) (Set.insert incPath openedSet)
    modifyIORef' (tsOpenedRev ts) (incPath :)

