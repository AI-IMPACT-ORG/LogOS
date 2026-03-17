{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Discipline.PortsAsDisplayed.Definitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Discipline gate: canonical LOG port 2-cats must be displayed + Σ-decorated.
--
-- This checks that the canonical `*2Cat` constructions in `LogOS.LT.LOG`
-- are definitionally equal to the canonical constructors from
-- `DisplayedThin2Cat` (so the proofs are literally `refl`).
--
-- This is intentionally brittle: if someone introduces a bespoke thin 2-category
-- instead of adding a displayed-port decoration, this module stops typechecking.

open import LogOS.Prelude using (Level; Setω; lzero; _⊔_; ⊤; tt; _≡_; refl)
open import LogOS.LT.DisplayedThin2Cat using
    ( DecoratedThin2Cat
    ; forgetDecorated
    )
open import LogOS.LT.Thin2Functor using (Thin2Functor)

import LogOS.LT.Ports.PortStack.Raw as PortStack

import LogOS.LT.LOG.Boundary2Cat as Boundary
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation
import LogOS.LT.LOG.Flow2Cat as Flow
import LogOS.LT.LOG.Contract2Cat as Contract
import LogOS.LT.LOG.EncodePort2Cat as Encode
import LogOS.LT.LOG.QuotePort2Cat as Quote
import LogOS.LT.LOG.BoundaryDecode2Cat as BoundaryDecode
import LogOS.LT.LOG.ImplementationDecode2Cat.Core as ImplementationDecode
import LogOS.LT.LOG.ImplementationContract2Cat.Core as ImplementationContract
import LogOS.LT.LOG.ImplementationFlow2Cat.Core as ImplementationFlow
import LogOS.LT.LOG.ArchitectureEncode2Cat as ArchitectureEncode
import LogOS.LT.LOG.ArchitectureQuote2Cat as ArchitectureQuote
import LogOS.LT.LOG.ArchitectureBulkBoundary2Cat as ArchitectureBulkBoundary

-- Boundary-only base --------------------------------------------------------

LOGArchitecture-self
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Boundary.LOGᴳ {ℓ} {ℓRel} {ℓCode} ≡ Boundary.LOGᴳ {ℓ} {ℓRel} {ℓCode}
LOGArchitecture-self = refl

-- Implementation layer over `LOGᴳ` -----------------------------------------

implementationLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Implementation.LOGᴳʳ {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (Implementation.ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})
implementationLayer-isDecorated = refl

-- Implementation-enriched port stacks over `LOGᴳ` ---------------------------

implementationContractLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ImplementationContract.LOGᴳʳ∂ {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat
      (PortStack.StackDisplayed (ImplementationContract.ImplementationContractStack {ℓ} {ℓRel} {ℓCode}))
implementationContractLayer-isDecorated = refl

implementationFlowLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ImplementationFlow.LOGᴳʳᶠ {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat
      (PortStack.StackDisplayed (ImplementationFlow.ImplementationFlowStack {ℓ} {ℓRel} {ℓCode}))
implementationFlowLayer-isDecorated = refl

-- Flow port -----------------------------------------------------------------

flowLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Flow.WithPort {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (Flow.FlowDisplayed {ℓ} {ℓRel} {ℓCode})
flowLayer-isDecorated = refl

forgetFlow-isForgetDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Flow.forget {ℓ} {ℓRel} {ℓCode}
    ≡
    forgetDecorated (Flow.FlowDisplayed {ℓ} {ℓRel} {ℓCode})
forgetFlow-isForgetDecorated = refl

-- Contract port -------------------------------------------------------------

contractLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Contract.WithPort {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (Contract.ContractDisplayed {ℓ} {ℓRel} {ℓCode})
contractLayer-isDecorated = refl

forgetContract-isForgetDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Contract.forget {ℓ} {ℓRel} {ℓCode}
    ≡
    forgetDecorated (Contract.ContractDisplayed {ℓ} {ℓRel} {ℓCode})
forgetContract-isForgetDecorated = refl

-- Encode port ---------------------------------------------------------------

encodeLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Encode.WithPort {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (Encode.EncodeDisplayed {ℓ} {ℓRel} {ℓCode})
encodeLayer-isDecorated = refl

forgetEncode-isForgetDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Encode.forget {ℓ} {ℓRel} {ℓCode}
    ≡
    forgetDecorated (Encode.EncodeDisplayed {ℓ} {ℓRel} {ℓCode})
forgetEncode-isForgetDecorated = refl

-- Quote law-port (flow + encode + linking law) -----------------------------

quoteLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Quote.WithPort {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (Quote.QuoteDisplayed {ℓ} {ℓRel} {ℓCode})
quoteLayer-isDecorated = refl

forgetQuote-isForgetDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Quote.forget {ℓ} {ℓRel} {ℓCode}
    ≡
    forgetDecorated (Quote.QuoteDisplayed {ℓ} {ℓRel} {ℓCode})
forgetQuote-isForgetDecorated = refl

-- Law-ports must provide explicit forgetful 2-functors to independent layers.
forgetQuoteFlow-typed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (Quote.WithPort {ℓ} {ℓRel} {ℓCode})
      (Flow.WithPort {ℓ} {ℓRel} {ℓCode})
forgetQuoteFlow-typed = Quote.forgetQuoteFlow

forgetQuoteEncode-typed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (Quote.WithPort {ℓ} {ℓRel} {ℓCode})
      (Encode.WithPort {ℓ} {ℓRel} {ℓCode})
forgetQuoteEncode-typed = Quote.forgetQuoteEncode

record SupportedArchitectureLayers (ℓ ℓRel ℓCode : Level) : Setω where
  field
    implementation
      : Implementation.LOGᴳʳ {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (Implementation.ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})

    implementationContract
      : ImplementationContract.LOGᴳʳ∂ {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat
          (PortStack.StackDisplayed
            (ImplementationContract.ImplementationContractStack {ℓ} {ℓRel} {ℓCode}))

    implementationFlow
      : ImplementationFlow.LOGᴳʳᶠ {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat
          (PortStack.StackDisplayed
            (ImplementationFlow.ImplementationFlowStack {ℓ} {ℓRel} {ℓCode}))

    flow
      : Flow.WithPort {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (Flow.FlowDisplayed {ℓ} {ℓRel} {ℓCode})

    contract
      : Contract.WithPort {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (Contract.ContractDisplayed {ℓ} {ℓRel} {ℓCode})

    encode
      : Encode.WithPort {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (Encode.EncodeDisplayed {ℓ} {ℓRel} {ℓCode})

    quoteLaw
      : Quote.WithPort {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (Quote.QuoteDisplayed {ℓ} {ℓRel} {ℓCode})

supportedArchitectureLayers
  : ∀ {ℓ ℓRel ℓCode : Level}
  → SupportedArchitectureLayers ℓ ℓRel ℓCode
supportedArchitectureLayers =
  record
    { implementation = implementationLayer-isDecorated
    ; implementationContract = implementationContractLayer-isDecorated
    ; implementationFlow = implementationFlowLayer-isDecorated
    ; flow = flowLayer-isDecorated
    ; contract = contractLayer-isDecorated
    ; encode = encodeLayer-isDecorated
    ; quoteLaw = quoteLayer-isDecorated
    }

-- Export one harmless witness so this module can be imported via the API
-- without re-exporting all internal discipline lemmas.
ok : ⊤ {ℓ = lzero}
ok = tt
