-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}

module Metamath.Check
  ( checkProof
  ) where

import Control.Exception (throwIO)
import Control.Monad (unless, when)
import qualified Data.ByteString as BS
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.Sequence (Seq (..), (|>))
import Data.Word (Word8)

import Metamath.Types

data Step
  = StepLabel !Label
  | StepSave
  | StepSaved !Int
  deriving (Show)

checkProof
  :: IntSet.IntSet
  -- ^ Variables set (interned symbols that are variables).
  -> Map.Map Label FloatingHyp
  -> Map.Map Label EssentialHyp
  -> Map.Map Label Assertion
  -- ^ Proven/usable assertions (axioms + checked theorems).
  -> Assertion
  -- ^ The theorem being checked.
  -> [Label]
  -- ^ Proof token stream (labels, or compressed proof tokens).
  -> IO ()
checkProof vars floating essential assertions thm proofTokens = do
  let hypLabels = foldr (\l s -> Map.insert l () s) Map.empty (asFloatHyps thm <> asEssHyps thm)
      isHyp l = Map.member l hypLabels

  steps <-
    case proofTokens of
      (t : _) | t == BS8.pack "(" -> decodeCompressed thm proofTokens
      _ -> pure (map StepLabel proofTokens)

  let push x st = x : st
      popN n st
        | n < 0 = throwIO (MMError "internal: negative pop")
        | otherwise = do
            (revArgs, rest) <- takeN n st
            pure (reverse revArgs, rest)

  let go :: [Expr] -> Seq Expr -> [Step] -> IO ()
      go stack saved = \case
        [] -> do
          case stack of
            [x] ->
              unless (x == asExpr thm) $
                throwIO (MMError ("proof of " <> BS8.unpack (asLabel thm) <> " proves a different statement"))
            _ ->
              throwIO (MMError ("proof of " <> BS8.unpack (asLabel thm) <> " leaves stack size " <> show (length stack)))
        (st : rest) ->
          case st of
            StepSave -> do
              case stack of
                [] -> throwIO (MMError "save (Z) with empty stack")
                (x : _) -> go stack (saved |> x) rest
            StepSaved k -> do
              case Seq.lookup k saved of
                Nothing -> throwIO (MMError ("saved ref out of range: " <> show k))
                Just x -> go (push x stack) saved rest
            StepLabel l ->
              if isHyp l
                then do
                  -- Push hypothesis expression (floating or essential).
                  case Map.lookup l floating of
                    Just fh -> go (push [fhTypecode fh, fhVar fh] stack) saved rest
                    Nothing ->
                      case Map.lookup l essential of
                        Just eh -> go (push (ehExpr eh) stack) saved rest
                        Nothing -> throwIO (MMError ("hypothesis label not found as $f/$e: " <> BS8.unpack l))
                else do
                  -- Disallow $f/$e outside the theorem frame.
                  when (Map.member l floating || Map.member l essential) $
                    throwIO (MMError ("out-of-scope hypothesis used in proof of " <> BS8.unpack (asLabel thm) <> ": " <> BS8.unpack l))
                  a <- case Map.lookup l assertions of
                    Nothing -> throwIO (MMError ("unknown/assertion label in proof: " <> BS8.unpack l))
                    Just x -> pure x
                  let arity = length (asFloatHyps a) + length (asEssHyps a)
                  (args, stack') <- popN arity stack
                  concl <- applyAssertion vars floating essential assertions l a args
                  go (push concl stack') saved rest

  go [] Seq.empty steps

applyAssertion
  :: IntSet.IntSet
  -> Map.Map Label FloatingHyp
  -> Map.Map Label EssentialHyp
  -> Map.Map Label Assertion
  -> Label
  -> Assertion
  -> [Expr]
  -> IO Expr
applyAssertion vars floating essential _assertions lbl a args = do
  let numF = length (asFloatHyps a)
      numE = length (asEssHyps a)
  unless (length args == numF + numE) $
    throwIO (MMError ("arity mismatch applying " <> BS8.unpack lbl))

  -- 1) Floating hypotheses determine substitution.
  subst <- buildSubst (asFloatHyps a) (take numF args) IntMap.empty

  -- 2) Disjoint variable restrictions.
  checkDisjoint vars subst (asDvPairs a)

  -- 3) Essential hypotheses must match after substitution.
  checkEss subst (asEssHyps a) (drop numF args)

  -- 4) Substituted conclusion.
  pure (substExpr subst (asExpr a))
  where
    buildSubst :: [Label] -> [Expr] -> IntMap.IntMap Expr -> IO (IntMap.IntMap Expr)
    buildSubst [] [] m = pure m
    buildSubst (flbl : flbls) (got : gots) m = do
      fh <- case Map.lookup flbl floating of
        Nothing -> throwIO (MMError ("missing $f hypothesis " <> BS8.unpack flbl <> " referenced by " <> BS8.unpack lbl))
        Just x -> pure x
      case got of
        [] ->
          throwIO (MMError ("empty expression for floating hyp " <> BS8.unpack flbl <> " of " <> BS8.unpack lbl))
        (gotTc : rhs) -> do
          let wantTc = fhTypecode fh
          unless (gotTc == wantTc) $
            throwIO (MMError ("typecode mismatch for " <> BS8.unpack lbl <> "/" <> BS8.unpack flbl))
          let v = fhVar fh
          case IntMap.lookup v m of
            Nothing -> buildSubst flbls gots (IntMap.insert v rhs m)
            Just prev ->
              if prev == rhs
                then buildSubst flbls gots m
                else throwIO (MMError ("inconsistent substitution for var applying " <> BS8.unpack lbl))
    buildSubst _ _ _ = throwIO (MMError ("internal: substitution arity mismatch for " <> BS8.unpack lbl))

    checkEss :: IntMap.IntMap Expr -> [Label] -> [Expr] -> IO ()
    checkEss _ [] [] = pure ()
    checkEss m (elbl : elbls) (got : gots) = do
      templ <- case Map.lookup elbl essential of
        Nothing -> throwIO (MMError ("missing $e hypothesis " <> BS8.unpack elbl <> " referenced by " <> BS8.unpack lbl))
        Just x -> pure (ehExpr x)
      let want = substExpr m templ
      unless (got == want) $
        throwIO (MMError ("essential hyp mismatch for " <> BS8.unpack lbl <> "/" <> BS8.unpack elbl))
      checkEss m elbls gots
    checkEss _ _ _ = throwIO (MMError ("internal: essential arity mismatch for " <> BS8.unpack lbl))

checkDisjoint :: IntSet.IntSet -> IntMap.IntMap Expr -> [(Sym, Sym)] -> IO ()
checkDisjoint vars subst pairs = do
  let substVars =
        IntMap.map
          (\rhs -> foldr (\t s -> if IntSet.member t vars then IntSet.insert t s else s) IntSet.empty rhs)
          subst
  mapM_ (checkPair substVars) pairs
  where
    checkPair sv (x, y) =
      case (IntMap.lookup x sv, IntMap.lookup y sv) of
        (Just vx, Just vy) ->
          unless (IntSet.null (IntSet.intersection vx vy)) $
            throwIO (MMError ("DV violation: variables share a symbol"))
        _ -> throwIO (MMError "DV pair refers to missing substitution var")

substExpr :: IntMap.IntMap Expr -> Expr -> Expr
substExpr subst = go id
  where
    go dl [] = dl []
    go dl (t : ts) =
      case IntMap.lookup t subst of
        Just rhs -> go (dl . (rhs ++)) ts
        Nothing -> go (dl . (t :)) ts

decodeCompressed :: Assertion -> [Label] -> IO [Step]
decodeCompressed thm toks =
  case toks of
    [] -> throwIO (MMError "empty compressed proof")
    (t0 : rest) -> do
      unless (t0 == BS8.pack "(") $
        throwIO (MMError "not a compressed proof (expected leading '(')")
      let (labels, rest') = span (/= BS8.pack ")") rest
      case rest' of
        [] -> throwIO (MMError "compressed proof missing closing ')'")
        (_close : codeToks) -> do
          let code = BS.concat codeToks
          when (BS8.elem '?' code) $
            throwIO (MMError "compressed proof contains '?' (incomplete proof)")
          let refs = asFloatHyps thm <> asEssHyps thm <> labels
          decodeCode refs code

decodeCode :: [Label] -> ByteString -> IO [Step]
decodeCode refs code = go 0 [] (BS.unpack code)
  where
    refsSeq :: Seq Label
    refsSeq = Seq.fromList refs
    nrefs :: Int
    nrefs = length refs

    a, t, u, y, z :: Word8
    a = fromIntegral (fromEnum 'A')
    t = fromIntegral (fromEnum 'T')
    u = fromIntegral (fromEnum 'U')
    y = fromIntegral (fromEnum 'Y')
    z = fromIntegral (fromEnum 'Z')

    go :: Int -> [Step] -> [Word8] -> IO [Step]
    go acc out [] = do
      unless (acc == 0) $
        throwIO (MMError "dangling compressed proof accumulator (missing A..T terminator?)")
      pure (reverse out)
    go acc out (ch : rest)
      | ch == z = do
          unless (acc == 0) $
            throwIO (MMError "compressed proof has 'Z' inside an encoded number")
          go 0 (StepSave : out) rest
      | ch >= u && ch <= y = do
          let digit = fromIntegral (ch - u + 1) -- 1..5
          go (acc * 5 + digit) out rest
      | ch >= a && ch <= t = do
          let n = acc * 20 + fromIntegral (ch - a + 1)
          unless (n > 0) $
            throwIO (MMError "decoded nonpositive proof reference")
          if n <= nrefs
            then
              case Seq.lookup (n - 1) refsSeq of
                Nothing -> throwIO (MMError "internal: bad refs index")
                Just lab -> go 0 (StepLabel lab : out) rest
            else do
              let k = n - nrefs - 1
              go 0 (StepSaved k : out) rest
      | otherwise =
          throwIO (MMError ("invalid compressed proof character: " <> show ch))

takeN :: Int -> [a] -> IO ([a], [a])
takeN 0 xs = pure ([], xs)
takeN n xs =
  case xs of
    [] -> throwIO (MMError "stack underflow")
    (x : rest) -> do
      (ys, rest') <- takeN (n - 1) rest
      pure (x : ys, rest')
