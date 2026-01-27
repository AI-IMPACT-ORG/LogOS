{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetTheory.SchemaTheorems where

-- Canonical ZF/ZFC axiom-schema witnesses, exposed with standard names.
-- These are lightweight, name-aligned wrappers over the existing ZF/ZFC packs.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel; kernelLike-fromKernel)

import LogOS.Domain.ZFC.SetTheory.Pack as Pack
import LogOS.Domain.ZFC.SetTheory.FormulaPack as Formula

module ZF
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (A : Pack.ZFAxioms (kernelLike-fromKernel K))
  where
  open Pack.ZFAxioms A public

  Extensionality = extensionality
  EmptySet = empty
  Pairing = pairing
  Union = union
  PowerSet = powerset
  Infinity = infinity
  SeparationSchema = separation
  ReplacementSchema = replacement
  Foundation = foundation

module ZFC
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (A : Pack.ZFCAxioms (kernelLike-fromKernel K))
  where
  open Pack.ZFCAxioms A public
  module ZFBase = ZF K zf
  open ZFBase public
    using
      ( Extensionality
      ; EmptySet
      ; Pairing
      ; Union
      ; PowerSet
      ; Infinity
      ; SeparationSchema
      ; ReplacementSchema
      ; Foundation
      )

  Choice = AC

module ZFᶠ
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (A : Formula.ZFAxiomsᶠ K)
  where
  open Formula.ZFAxiomsᶠ A public

  Extensionality = extensionality
  EmptySet = empty
  Pairing = pairing
  Union = union
  PowerSet = powerset
  Infinity = infinity
  SeparationSchema = separationᶠ
  ReplacementSchema = replacementᶠ
  Foundation = foundation

module ZFCᶠ
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (A : Formula.ZFCAxiomsᶠ K)
  where
  open Formula.ZFCAxiomsᶠ A public
  module ZFBase = ZFᶠ K zf
  open ZFBase public
    using
      ( Extensionality
      ; EmptySet
      ; Pairing
      ; Union
      ; PowerSet
      ; Infinity
      ; SeparationSchema
      ; ReplacementSchema
      ; Foundation
      )

  Choice = AC
