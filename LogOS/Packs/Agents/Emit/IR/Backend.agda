{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.IR.Backend where

open import LogOS.Prelude.List using (List)
open import LogOS.Prelude.Maybe using (Maybe)
open import LogOS.Prelude.String using (String)

record Backend : Set1 where
  field
    Expr : Set
    Arg : Set
    Slice : Set
    Target : Set
    Stmt : Set
    Module : Set

    raw : String → Expr
    var : String → Expr
    stringLit : String → Expr
    attr : Expr → String → Expr
    call : Expr → List Arg → Expr
    binOp : String → Expr → Expr → Expr
    index : Expr → Expr → Expr
    tuple : List Expr → Expr
    subscript : Expr → List Slice → Expr

    argPos : Expr → Arg
    argKw : String → Expr → Arg

    slice : Maybe Expr → Maybe Expr → Slice
    sliceIndex : Expr → Slice

    targetName : String → Target
    targetTuple : List String → Target

    blank : Stmt
    comment : String → Stmt
    importAs : String → String → Stmt
    assign : String → Expr → Stmt
    assignExpr : Expr → Expr → Stmt
    exprStmt : Expr → Stmt
    return : Expr → Stmt
    def : String → List String → List Stmt → Stmt
    forIn : Target → Expr → List Stmt → Stmt
    withAs : Expr → String → List Stmt → Stmt
    ifStmt : Expr → List Stmt → List Stmt → Stmt
    mkModule : List Stmt → Module
    renderModule : Module → String
