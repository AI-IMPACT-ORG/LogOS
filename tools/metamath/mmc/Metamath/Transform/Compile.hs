-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

-- | Metamath compile transformer.
--
-- Consumes a statement stream ('Metamath.Port.MM') and emits assertion records
-- to an artifact port ('Metamath.Artifact').
module Metamath.Transform.Compile
  ( CompileConfig(..)
  , St(..)
  , st0
  , compileStream
  ) where

import Control.Exception (throwIO)
import Control.Monad (forM, forM_, unless, when)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO (Handle)

import Metamath.Artifact (writeAssertionRecord)
import Metamath.Check (checkProof)
import Metamath.Intern (Interner, intern)
import Metamath.Port.MM (Stmt (..))
import Metamath.Stream (Stream (..))
import Metamath.Types

data CompileConfig = CompileConfig
  { ccCheckProofs :: !Bool
  , ccMaxAssertions :: !(Maybe Int)
  , ccProgressEvery :: !(Maybe Int)
  }

data St = St
  { stConsts :: !IntSet.IntSet
  , stVars :: !IntSet.IntSet
  , stFloating :: !(Map.Map Label FloatingHyp)
  , stEssential :: !(Map.Map Label EssentialHyp)
  , stActiveFRev :: ![FloatingHyp]
  , stActiveERev :: ![EssentialHyp]
  , stActiveDRev :: ![[Sym]]
  , stLenF :: !Int
  , stLenE :: !Int
  , stLenD :: !Int
  , stMarkers :: ![(Int, Int, Int)]
  , stAssertions :: !(Map.Map Label Assertion)
  , stUsedLabels :: !(Set.Set Label)
  , stCount :: !Int
  , stCountA :: !Int
  , stCountP :: !Int
  }

st0 :: St
st0 =
  St
    { stConsts = IntSet.empty
    , stVars = IntSet.empty
    , stFloating = Map.empty
    , stEssential = Map.empty
    , stActiveFRev = []
    , stActiveERev = []
    , stActiveDRev = []
    , stLenF = 0
    , stLenE = 0
    , stLenD = 0
    , stMarkers = []
    , stAssertions = Map.empty
    , stUsedLabels = Set.empty
    , stCount = 0
    , stCountA = 0
    , stCountP = 0
    }

compileStream :: Stream Stmt -> Interner -> Handle -> CompileConfig -> St -> IO St
compileStream stmts interner hDb cfg = go
  where
    go st =
      case ccMaxAssertions cfg of
        Just mx | mx > 0 && stCount st >= mx -> pure st
        _ -> do
          mstmt <- pull stmts
          case mstmt of
            Nothing -> do
              unless (null (stMarkers st)) $
                throwIO (MMError ("unclosed scopes at EOF: " <> show (length (stMarkers st))))
              pure st
            Just StScopeOpen ->
              go (pushScope st)
            Just StScopeClose -> do
              when (null (stMarkers st)) $
                throwIO (MMError "unmatched $} (scope underflow)")
              go (popScope (ccCheckProofs cfg) st)
            Just (StConsts toks) ->
              addConsts interner toks st >>= go
            Just (StVars toks) ->
              addVars interner toks st >>= go
            Just (StDisjoint toks) ->
              addDisjoint interner toks st >>= go
            Just (StFloating label body) ->
              addFloating interner label body st >>= go
            Just (StEssential label body) ->
              addEssential interner label body st >>= go
            Just (StAxiom label exprToks) ->
              addAssertion interner hDb cfg label exprToks Nothing st >>= go
            Just (StProvable label exprToks proofToks) ->
              addAssertion interner hDb cfg label exprToks (Just proofToks) st >>= go
            Just StIgnore ->
              throwIO (MMError "internal: StIgnore reached compileStream (run Metamath.Transform.Normalize.dropIgnored)")

pushScope :: St -> St
pushScope st =
  st { stMarkers = (stLenF st, stLenE st, stLenD st) : stMarkers st }

popScope :: Bool -> St -> St
popScope keepHyps st =
  case stMarkers st of
    [] -> st -- unreachable: 'compileStream' checks underflow before calling 'popScope'
    ((lf, le, ld) : ms) ->
      st
        { stFloating = floating'
        , stEssential = essential'
        , stActiveFRev = drop df (stActiveFRev st)
        , stActiveERev = drop de (stActiveERev st)
        , stActiveDRev = drop (stLenD st - ld) (stActiveDRev st)
        , stLenF = lf
        , stLenE = le
        , stLenD = ld
        , stMarkers = ms
        }
      where
        df = stLenF st - lf
        de = stLenE st - le
        removedF = take df (stActiveFRev st)
        removedE = take de (stActiveERev st)
        floating' =
          if keepHyps
            then stFloating st
            else foldr (Map.delete . fhLabel) (stFloating st) removedF
        essential' =
          if keepHyps
            then stEssential st
            else foldr (Map.delete . ehLabel) (stEssential st) removedE

registerLabel :: Label -> St -> IO St
registerLabel lbl st =
  if Set.member lbl (stUsedLabels st)
    then throwIO (MMError ("duplicate label: " <> BS8.unpack lbl))
    else pure st { stUsedLabels = Set.insert lbl (stUsedLabels st) }

addConsts :: Interner -> [ByteString] -> St -> IO St
addConsts interner toks st0' = do
  let vars = stVars st0'
  consts <- foldM' (stConsts st0') toks $ \acc t -> do
    s <- intern interner t
    when (IntSet.member s vars) $
      throwIO (MMError ("symbol declared as both $v and $c: " <> BS8.unpack t))
    pure (IntSet.insert s acc)
  pure st0' { stConsts = consts }

addVars :: Interner -> [ByteString] -> St -> IO St
addVars interner toks st0' = do
  let consts = stConsts st0'
  vars <- foldM' (stVars st0') toks $ \acc t -> do
    s <- intern interner t
    when (IntSet.member s consts) $
      throwIO (MMError ("symbol declared as both $c and $v: " <> BS8.unpack t))
    pure (IntSet.insert s acc)
  pure st0' { stVars = vars }

addDisjoint :: Interner -> [ByteString] -> St -> IO St
addDisjoint interner toks st0' = do
  syms <- mapM (intern interner) toks
  forM_ syms $ \s ->
    unless (IntSet.member s (stVars st0')) $
      throwIO (MMError "$d lists non-variable symbol")
  let ds = syms : stActiveDRev st0'
  pure st0' { stActiveDRev = ds, stLenD = stLenD st0' + 1 }

addFloating :: Interner -> Label -> [ByteString] -> St -> IO St
addFloating interner label body st0' =
  case body of
    [tcTok, varTok] -> do
      st1 <- registerLabel label st0'
      tc <- intern interner tcTok
      v <- intern interner varTok
      unless (IntSet.member tc (stConsts st0')) $
        throwIO (MMError ("$f typecode is not a declared constant: " <> BS8.unpack tcTok))
      unless (IntSet.member v (stVars st0')) $
        throwIO (MMError ("$f variable is not a declared variable: " <> BS8.unpack varTok))
      let fh = FloatingHyp { fhLabel = label, fhTypecode = tc, fhVar = v }
      pure
        st1
          { stFloating = Map.insert label fh (stFloating st1)
          , stActiveFRev = fh : stActiveFRev st1
          , stLenF = stLenF st1 + 1
          }
    _ ->
      throwIO (MMError ("malformed $f statement " <> BS8.unpack label))

addEssential :: Interner -> Label -> [ByteString] -> St -> IO St
addEssential interner label exprToks st0' = do
  st1 <- registerLabel label st0'
  expr <- internExpr interner st0' ("$e " <> BS8.unpack label) exprToks
  let eh = EssentialHyp { ehLabel = label, ehExpr = expr }
  pure
    st1
      { stEssential = Map.insert label eh (stEssential st1)
      , stActiveERev = eh : stActiveERev st1
      , stLenE = stLenE st1 + 1
      }

addAssertion
  :: Interner
  -> Handle
  -> CompileConfig
  -> Label
  -> [ByteString]
  -> Maybe [Label]
  -> St
  -> IO St
addAssertion interner hDb cfg label exprToks mProof st0' = do
  stL <- registerLabel label st0'
  expr <- internExpr interner st0' (ctx <> " " <> BS8.unpack label) exprToks

  let mv = mandatoryVars (stVars st0') expr (stActiveERev st0')
      mandF = mandatoryFloating mv (stActiveFRev st0')
      mandE = mandatoryEssential (stActiveERev st0')
      dvPairs = disjointPairs mv (stActiveDRev st0')

      a =
        Assertion
          { asLabel = label
          , asExpr = expr
          , asFloatHyps = mandF
          , asEssHyps = mandE
          , asDvPairs = dvPairs
          }

  floatForms <-
    forM mandF $ \flbl -> do
      fh <- case Map.lookup flbl (stFloating st0') of
        Nothing -> throwIO (MMError "internal: missing floating hyp for mandatory frame")
        Just x -> pure x
      pure [fhTypecode fh, fhVar fh]
  essForms <-
    forM mandE $ \elbl -> do
      eh <- case Map.lookup elbl (stEssential st0') of
        Nothing -> throwIO (MMError "internal: missing essential hyp for mandatory frame")
        Just x -> pure x
      pure (ehExpr eh)

  let hypsFormulas = floatForms <> essForms
      conclFormula = expr

      assertions0 = stAssertions stL

  case mProof of
    Nothing -> pure ()
    Just proofToks ->
      when (ccCheckProofs cfg) $
        checkProof (stVars st0') (stFloating st0') (stEssential st0') assertions0 a proofToks

  -- Only retain the assertion environment if we are going to use it for proof checking.
  let assertions1 =
        if ccCheckProofs cfg
          then Map.insert label a assertions0
          else assertions0

      st1 = stL { stAssertions = assertions1 }

  writeAssertionRecord hDb label hypsFormulas conclFormula

  let st2 =
        st1
          { stCount = stCount st1 + 1
          , stCountA = if mProof == Nothing then stCountA st1 + 1 else stCountA st1
          , stCountP = if mProof /= Nothing then stCountP st1 + 1 else stCountP st1
          }

  case ccMaxAssertions cfg of
    Nothing -> progress st2 >> pure st2
    Just mx ->
      if stCount st2 >= mx
        then pure st2
        else progress st2 >> pure st2
  where
    ctx = if mProof == Nothing then "$a" else "$p"
    progress stx =
      case ccProgressEvery cfg of
        Nothing -> pure ()
        Just n ->
          when (n > 0 && stCount stx `mod` n == 0) $
            putStrLn ("... " <> show (stCount stx) <> " assertions; latest: " <> BS8.unpack label)

internExpr :: Interner -> St -> String -> [ByteString] -> IO Expr
internExpr interner st0' where_ toks = do
  when (null toks) $
    throwIO (MMError ("empty expression in " <> where_))
  syms <- mapM (intern interner) toks
  case syms of
    [] ->
      throwIO (MMError ("internal: empty interned expression in " <> where_))
    (tc : rest) -> do
      unless (IntSet.member tc (stConsts st0')) $
        throwIO (MMError ("expression typecode is not a declared constant (" <> where_ <> ")"))
      let ok s = IntSet.member s (stConsts st0') || IntSet.member s (stVars st0')
      forM_ rest $ \s ->
        unless (ok s) $
          throwIO (MMError ("unknown symbol in expression (" <> where_ <> ")"))
      pure (tc : rest)

mandatoryVars :: IntSet.IntSet -> Expr -> [EssentialHyp] -> IntSet.IntSet
mandatoryVars vars expr ess =
  foldr add (varsInExpr vars expr) ess
  where
    add eh acc = IntSet.union acc (varsInExpr vars (ehExpr eh))

varsInExpr :: IntSet.IntSet -> Expr -> IntSet.IntSet
varsInExpr vars = foldr (\t s -> if IntSet.member t vars then IntSet.insert t s else s) IntSet.empty

mandatoryFloating :: IntSet.IntSet -> [FloatingHyp] -> [Label]
mandatoryFloating mv activeFRev =
  reverse [fhLabel fh | fh <- activeFRev, IntSet.member (fhVar fh) mv]

mandatoryEssential :: [EssentialHyp] -> [Label]
mandatoryEssential activeERev = reverse (map ehLabel activeERev)

disjointPairs :: IntSet.IntSet -> [[Sym]] -> [(Sym, Sym)]
disjointPairs mv activeDRev =
  Set.toAscList $
    Set.unions
      [ Set.fromList (pairs (filter (`IntSet.member` mv) vs))
      | vs <- activeDRev
      ]
  where
    pairs xs =
      [ order (xs !! i) (xs !! j)
      | i <- [0 .. length xs - 1]
      , j <- [i + 1 .. length xs - 1]
      ]
    order a b = if a < b then (a, b) else (b, a)

foldM' :: a -> [b] -> (a -> b -> IO a) -> IO a
foldM' z xs f = go z xs
  where
    go acc [] = pure acc
    go acc (y : ys) = do
      acc' <- f acc y
      go acc' ys
