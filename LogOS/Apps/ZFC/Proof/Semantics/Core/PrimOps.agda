{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Core.PrimOps where

open import LogOS.Prelude using
  ( Level
  ; _≡_
  ; ⊤
  ; tt
  ; _×_
  ; _⊎_
  ; Σ
  ; _,_
  ; fst
  ; snd
  ; inj₁
  ; inj₂
  ; refl
  ; cong
  ; cong₂
  ; lift
  ; lower
  ; ⊥-elim
  ; ¬_
  )
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel; Code; decode)
import LogOS.LT.Stack as LTStack

open import LogOS.Apps.ZFC.Proof.Syntax using
  ( Term
  ; var; emptyT; pairT; unionT; powerT; succT; omegaT
  )

open import LogOS.Apps.ZFC.Proof.Semantics.Core.ModelDef using (Model)
import LogOS.Apps.ZFC.Stack.ZFCore.PrimitiveStack as PrimitiveStack

module ForModel {ℓ : Level} (M : Model {ℓ}) where
  open Model M
  open FO.D using (SuccV)

  -- The primitive constructor stack (macro/program kernel surface).
  module Prim = PrimitiveStack.Primitive ctx coreSig powSig omegaSig
  open Prim public using
    ( PrimOp
    ; PrimCode
    ; primStack
    ; PrimProgramK
    ; emptyOp
    ; powersetOp
    ; unionOp
    ; pairOp
    ; zeroOp
    ; succOp
    ; omegaOp
    )

  -- ------------------------------------------------------------------------

  emptySet-empty : ∀ z → ¬ (z ∈ emptySet)
  emptySet-empty = empty-spec

  zeroSet-empty : ∀ z → ¬ (z ∈ zeroSet)
  zeroSet-empty = emptySet-empty

  zero≈empty : zeroSet ≈ emptySet
  zero≈empty =
    ( (λ z z∈0 → ⊥-elim (zeroSet-empty z z∈0))
    , (λ z z∈e → ⊥-elim (emptySet-empty z z∈e))
    )

  unionVE : LTStack.ViewExpr primStack LTStack.bndS
  unionVE = LTStack.pullback (λ x → lift (lower x)) (LTStack.prim unionOp)

  unionVE-preserves-≈
    : ∀ {x y}
    → x ≈ y
    → LTStack.evalBoundaryExpr unionVE x ≈ LTStack.evalBoundaryExpr unionVE y
  unionVE-preserves-≈ {x} {y} x≈y =
    ( toUnion≈
    , fromUnion≈
    )
    where
      toUnion≈ : ∀ z → z ∈ LTStack.evalBoundaryExpr unionVE x → z ∈ LTStack.evalBoundaryExpr unionVE y
      toUnion≈ z z∈ux =
        let
          (w , (w∈x , z∈w)) = _↔_.to (union-spec x z) z∈ux
        in
        _↔_.from (union-spec y z)
          (w , (fst x≈y w w∈x , z∈w))

      fromUnion≈ : ∀ z → z ∈ LTStack.evalBoundaryExpr unionVE y → z ∈ LTStack.evalBoundaryExpr unionVE x
      fromUnion≈ z z∈uy =
        let
          (w , (w∈y , z∈w)) = _↔_.to (union-spec y z) z∈uy
        in
        _↔_.from (union-spec x z)
          (w , (snd x≈y w w∈y , z∈w))

  unionEndo : LTStack.BoundaryEndo primStack
  unionEndo = LTStack.mkBoundaryEndo unionVE unionVE-preserves-≈

  powVE : LTStack.ViewExpr primStack LTStack.bndS
  powVE = LTStack.pullback (λ x → lift (lower x)) (LTStack.prim powersetOp)

  powVE-preserves-≈
    : ∀ {x y}
    → x ≈ y
    → LTStack.evalBoundaryExpr powVE x ≈ LTStack.evalBoundaryExpr powVE y
  powVE-preserves-≈ {x} {y} x≈y =
    ( toPow≈
    , fromPow≈
    )
    where
      toPow≈ : ∀ z → z ∈ LTStack.evalBoundaryExpr powVE x → z ∈ LTStack.evalBoundaryExpr powVE y
      toPow≈ z z∈px =
        let
          subsetX = _↔_.to (powerset-spec x z) z∈px
        in
        _↔_.from (powerset-spec y z)
          (λ w w∈z → fst x≈y w (subsetX w w∈z))

      fromPow≈ : ∀ z → z ∈ LTStack.evalBoundaryExpr powVE y → z ∈ LTStack.evalBoundaryExpr powVE x
      fromPow≈ z z∈py =
        let
          subsetY = _↔_.to (powerset-spec y z) z∈py
        in
        _↔_.from (powerset-spec x z)
          (λ w w∈z → snd x≈y w (subsetY w w∈z))

  powEndo : LTStack.BoundaryEndo primStack
  powEndo = LTStack.mkBoundaryEndo powVE powVE-preserves-≈

  succVE : LTStack.ViewExpr primStack LTStack.bndS
  succVE = LTStack.pullback (λ x → lift (lower x)) (LTStack.prim succOp)

  succVE-preserves-≈
    : ∀ {x y}
    → x ≈ y
    → LTStack.evalBoundaryExpr succVE x ≈ LTStack.evalBoundaryExpr succVE y
  succVE-preserves-≈ {x} {y} x≈y =
    ( toSucc≈
    , fromSucc≈
    )
    where
      toSucc≈ : ∀ z → z ∈ succSet x → z ∈ succSet y
      toSucc≈ z z∈sx with _↔_.to (succ-spec x z) z∈sx
      ... | inj₁ z∈x =
        _↔_.from (succ-spec y z) (inj₁ (fst x≈y z z∈x))
      ... | inj₂ z≈x =
        _↔_.from (succ-spec y z) (inj₂ (trans≈ z≈x x≈y))

      fromSucc≈ : ∀ z → z ∈ succSet y → z ∈ succSet x
      fromSucc≈ z z∈sy with _↔_.to (succ-spec y z) z∈sy
      ... | inj₁ z∈y =
        _↔_.from (succ-spec x z) (inj₁ (snd x≈y z z∈y))
      ... | inj₂ z≈y =
        _↔_.from (succ-spec x z) (inj₂ (trans≈ z≈y (sym≈ x≈y)))

  succEndo : LTStack.BoundaryEndo primStack
  succEndo = LTStack.mkBoundaryEndo succVE succVE-preserves-≈

  -- Compile terms into the ZF constructor macro-kernel (`PrimProgramK`).
  --
  -- This makes the transformer stack structure explicit: term evaluation is the
  -- decoding of a `Program` over the primitive constructor stack.
  compileTerm : Term → Valuation → Code PrimProgramK
  compileTerm (var n) ρ =
    LTStack.mkProgram
      LTStack.bndS
      LTStack.idBnd
      (lift (ρ n))
  compileTerm emptyT ρ =
    LTStack.mkProgram
      (LTStack.opS emptyOp)
      (LTStack.prim emptyOp)
      (lift tt)
  compileTerm omegaT ρ =
    LTStack.mkProgram
      (LTStack.opS omegaOp)
      (LTStack.prim omegaOp)
      (lift tt)
  compileTerm (unionT t) ρ with compileTerm t ρ
  ... | LTStack.mkProgram σ V x =
    LTStack.mkProgram
      σ
      (LTStack.post unionEndo V)
      x
  compileTerm (powerT t) ρ with compileTerm t ρ
  ... | LTStack.mkProgram σ V x =
    LTStack.mkProgram
      σ
      (LTStack.post powEndo V)
      x
  compileTerm (succT t) ρ with compileTerm t ρ
  ... | LTStack.mkProgram σ V x =
    LTStack.mkProgram
      σ
      (LTStack.post succEndo V)
      x
  compileTerm (pairT t u) ρ with compileTerm t ρ | compileTerm u ρ
  ... | LTStack.mkProgram σ V x | LTStack.mkProgram τ W y =
    LTStack.mkProgram
      (σ LTStack.×S τ)
      ( LTStack.pullback
          (λ p →
            lift
              ( LTStack.decodeProgram {S = primStack} (LTStack.mkProgram σ V (fst p))
              , LTStack.decodeProgram {S = primStack} (LTStack.mkProgram τ W (snd p))
              ))
          (LTStack.prim pairOp)
      )
      (x , y)

  -- Compilation is semantics-preserving.
  decode-compileTerm : ∀ (t : Term) (ρ : Valuation) → decode PrimProgramK (compileTerm t ρ) ≡ evalTerm t ρ
  decode-compileTerm (var n) ρ = refl
  decode-compileTerm emptyT ρ = refl
  decode-compileTerm omegaT ρ = refl
  decode-compileTerm (unionT t) ρ = cong unionSet (decode-compileTerm t ρ)
  decode-compileTerm (powerT t) ρ = cong powersetSet (decode-compileTerm t ρ)
  decode-compileTerm (succT t) ρ = cong (μ SuccV) (decode-compileTerm t ρ)
  decode-compileTerm (pairT t u) ρ =
    cong₂ pairSet (decode-compileTerm t ρ) (decode-compileTerm u ρ)
