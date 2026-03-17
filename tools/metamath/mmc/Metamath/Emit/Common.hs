-- LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

{-# LANGUAGE StrictData #-}

-- | Small shared helpers for Haskell-side Agda artifact emission.
--
-- These utilities are intentionally small and intentionally formatting-oriented:
-- they encode conventions used by both `emit-agda` and `export-agda-runtime`
-- code generation so the generated modules stay consistent.
module Metamath.Emit.Common
  ( agdaLicenseHeader
  , agdaModuleHeader
  , agdaKernelPrelude
  , agdaFormulaTypeDecl
  , pad4
  , agdaNatPat
  , agdaListNat
  , agdaListFormula
  , agdaListListFormula
  , agdaString
  , symbolIndexComments
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import qualified Data.List as List

-- | Canonical Agda header used by generated modules.
agdaLicenseHeader :: [String]
agdaLicenseHeader =
  [ "{-"
  , "LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI"
  , "Copyright (C) 2026 AI.IMPACT GmbH"
  , "SPDX-License-Identifier: GPL-3.0-only"
  , "-}"
  ]

-- | Canonical module preface with a shared shape.
agdaModuleHeader :: String -> Bool -> [String]
agdaModuleHeader moduleName safe =
  agdaLicenseHeader
    <> [ "" ]
    <> (if safe then ["{-# OPTIONS --safe #-}"] else [])
    <> [ "module " <> moduleName <> " where" ]

-- | Shared kernel imports and list notation used across all generated Agda
-- Metamath modules.
agdaKernelPrelude :: [String]
agdaKernelPrelude =
  [ "open import LogOS.Prelude"
  , "open import LogOS.Prelude.List using (List; []; _∷_)"
  , ""
  ]

-- | Canonical formula declaration used by generated DB modules.
agdaFormulaTypeDecl :: [String]
agdaFormulaTypeDecl =
  [ "-- Formulas are token lists (symbols are interned as Nat indices)."
  , "Formula : Set"
  , "Formula = List ℕ"
  , ""
  ]

pad4 :: Int -> String
pad4 n =
  let s = show n
   in replicate (4 - length s) '0' <> s

agdaNatPat :: Int -> String
agdaNatPat 0 = "zero"
agdaNatPat k = "suc (" <> agdaNatPat (k - 1) <> ")"

agdaListNat :: [Int] -> String
agdaListNat [] = "[]"
agdaListNat xs = "(" <> List.intercalate " ∷ " (map show xs) <> " ∷ []" <> ")"

agdaListFormula :: [[Int]] -> String
agdaListFormula [] = "[]"
agdaListFormula rows = "(" <> List.intercalate " ∷ " (map agdaListNat rows) <> " ∷ []" <> ")"

agdaListListFormula :: [[[Int]]] -> String
agdaListListFormula [] = "[]"
agdaListListFormula rows = "(" <> List.intercalate " ∷ " (map agdaListFormula rows) <> " ∷ []" <> ")"

agdaString :: String -> String
agdaString s = "\"" <> concatMap esc s <> "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\r' = "\\r"
    esc '\t' = "\\t"
    esc c = [ c ]

-- | Emit list comments for symbol tables.
symbolIndexComments :: [ByteString] -> [String]
symbolIndexComments syms =
  [ "-- " <> show i <> ": " <> BS8.unpack s | (i, s) <- zip [0 :: Int ..] syms ]
