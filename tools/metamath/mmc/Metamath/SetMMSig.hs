{-# LANGUAGE StrictData #-}

module Metamath.SetMMSig
  ( setMMSigBlock
  ) where

import qualified Data.ByteString.Char8 as BS8
import qualified Data.List as List
import Data.ByteString (ByteString)

lookupSymIx :: String -> [ByteString] -> Maybe Int
lookupSymIx s syms = List.elemIndex (BS8.pack s) syms

setMMSigBlock :: [ByteString] -> [String]
setMMSigBlock syms =
  case do
    iTc  <- lookupSymIx "|-" syms
    iWff <- lookupSymIx "wff" syms
    iSet <- lookupSymIx "set" syms
    iLP  <- lookupSymIx "(" syms
    iRP  <- lookupSymIx ")" syms
    iImp <- lookupSymIx "->" syms
    iAnd <- lookupSymIx "/\\" syms
    iOr  <- lookupSymIx "\\/" syms
    iIff <- lookupSymIx "<->" syms
    iNot <- lookupSymIx "-." syms
    iAll <- lookupSymIx "A." syms
    iEx  <- lookupSymIx "E." syms
    iIn  <- lookupSymIx "e." syms
    iEq  <- lookupSymIx "=" syms
    pure
      ( iTc
      , iWff
      , iSet
      , iLP
      , iRP
      , iImp
      , iAnd
      , iOr
      , iIff
      , iNot
      , iAll
      , iEx
      , iIn
      , iEq
      )
    of
    Nothing ->
      [ "-- NOTE: `setMMSig` omitted (Set.MM FO-fragment tokens not present)." ]
    Just (iTc, iWff, iSet, iLP, iRP, iImp, iAnd, iOr, iIff, iNot, iAll, iEx, iIn, iEq) ->
      [ ""
      , "open import LogOS.Apps.ZFC.Metamath.SetMM as SetMM using"
      , "  ( Sig"
      , "  ; tc⊢ ; tcWff ; tcSet"
      , "  ; tokLParen ; tokRParen"
      , "  ; tokImp ; tokAnd ; tokOr ; tokIff"
      , "  ; tokNot ; tokAll ; tokEx"
      , "  ; tokIn ; tokEq"
      , "  )"
      , ""
      , "-- Set.MM token signature (derived from the symbol table; see below)."
      , "setMMSig : SetMM.Sig"
      , "setMMSig ="
      , "  record"
      , "    { tc⊢ = " <> show iTc
      , "    ; tcWff = " <> show iWff
      , "    ; tcSet = " <> show iSet
      , "    ; tokLParen = " <> show iLP
      , "    ; tokRParen = " <> show iRP
      , "    ; tokImp = " <> show iImp
      , "    ; tokAnd = " <> show iAnd
      , "    ; tokOr = " <> show iOr
      , "    ; tokIff = " <> show iIff
      , "    ; tokNot = " <> show iNot
      , "    ; tokAll = " <> show iAll
      , "    ; tokEx = " <> show iEx
      , "    ; tokIn = " <> show iIn
      , "    ; tokEq = " <> show iEq
      , "    }"
      , ""
      ]
