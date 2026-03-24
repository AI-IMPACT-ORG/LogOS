{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.QuotePort2Cat.Displayed where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_)
open import LogOS.LT.HomFlow using (KernelHomFlow; idKernelHomFlow; composeKernelHomFlow)
import LogOS.LT.LOG.Flow2Cat as Flow2Cat
import LogOS.LT.LOG.EncodePort2Cat as Encode2Cat
open import LogOS.LT.Thin2Functor using (Thin2Functor; _∘F_)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat; mapDecorated)

import LogOS.LT.LOG.QuotePort2Cat.FlowEncodeLayer as FlowEncodeLayer
import LogOS.LT.LOG.QuotePort2Cat.Port as Port

open Port using (QuotePort; GC; EK)
open Port.QuotePort

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data QuoteTag : Set where
  quoteTag : QuoteTag

private
  flowPort
    : ∀ {ℓ ℓRel ℓCode : Level}
    → PortStack.HasPort
        (PortStack.SingletonPort.entry (Flow2Cat.singleton {ℓ} {ℓRel} {ℓCode}))
        (FlowEncodeLayer.FlowEncodeStack {ℓ} {ℓRel} {ℓCode})
  flowPort {ℓ} {ℓRel} {ℓCode} =
    PortStack.hasHead
      {ps = PortStack.SingletonPort.stack (Encode2Cat.singleton {ℓ} {ℓRel} {ℓCode})}

  encodePort
    : ∀ {ℓ ℓRel ℓCode : Level}
    → PortStack.HasPort
        (PortStack.SingletonPort.entry (Encode2Cat.singleton {ℓ} {ℓRel} {ℓCode}))
        (FlowEncodeLayer.FlowEncodeStack {ℓ} {ℓRel} {ℓCode})
  encodePort {ℓ} {ℓRel} {ℓCode} =
    PortStack.hasThere
      {S = PortStack.SingletonPort.stack (Encode2Cat.singleton {ℓ} {ℓRel} {ℓCode})}
      PortStack.hasSingleton

record QuoteLaw {ℓ ℓRel ℓCode : Level} {K K' : Kernel ℓ ℓRel ℓCode}
  (h : KernelHom K K')
  (QP  : QuotePort K)
  (QP' : QuotePort K')
  : Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode) where
  field
    flow   : KernelHomFlow (GC QP) (GC QP') h
    encode : Encode2Cat.EncodeLaw h (EK QP) (EK QP')

open QuoteLaw public

idQuoteLaw
  : ∀ {ℓ ℓRel ℓCode : Level} {K : Kernel ℓ ℓRel ℓCode}
  → (QP : QuotePort K)
  → QuoteLaw (idKernelHom K) QP QP
idQuoteLaw QP =
  record
    { flow = idKernelHomFlow (GC QP)
    ; encode = Encode2Cat.idEncodeLaw (EK QP)
    }

composeQuoteLaw
  : ∀ {ℓ ℓRel ℓCode : Level} {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
    {QP₁ : QuotePort K₁}
    {QP₂ : QuotePort K₂}
    {QP₃ : QuotePort K₃}
  → QuoteLaw f QP₁ QP₂
  → QuoteLaw g QP₂ QP₃
  → QuoteLaw (g ∘ f) QP₁ QP₃
composeQuoteLaw cf cg =
  record
    { flow = composeKernelHomFlow (flow cf) (flow cg)
    ; encode = Encode2Cat.composeEncodeLaw (encode cf) (encode cg)
    }

QuoteDisplayed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOG {ℓ} {ℓRel} {ℓCode})
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
QuoteDisplayed {ℓ} {ℓRel} {ℓCode} =
  record
    { Ob = QuotePort
    ; HomD = λ {K} {K'} (h : KernelHom K K') QP QP' → QuoteLaw h QP QP'
    ; idD = idQuoteLaw
    ; compD = λ cf cg → composeQuoteLaw cf cg
    }

module Quote2Cat {ℓ ℓRel ℓCode : Level} =
  Template.SingletonLayer
    {Tag = QuoteTag}
    (QuoteDisplayed {ℓ} {ℓRel} {ℓCode})

QuoteLayer
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) QuoteTag
QuoteLayer {ℓ} {ℓRel} {ℓCode} =
  Quote2Cat.portSig {ℓ} {ℓRel} {ℓCode}

open Quote2Cat public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)

forgetQuoteFlowEncode
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (WithPort {ℓ} {ℓRel} {ℓCode})
      (PortStack.StackCat (FlowEncodeLayer.FlowEncodeStack {ℓ} {ℓRel} {ℓCode}))
forgetQuoteFlowEncode {ℓ} {ℓRel} {ℓCode} =
  mapDecorated
    (QuoteDisplayed {ℓ} {ℓRel} {ℓCode})
    (PortStack.StackDisplayed (FlowEncodeLayer.FlowEncodeStack {ℓ} {ℓRel} {ℓCode}))
    (λ {A} → λ QP → (QuotePort.GC QP , QuotePort.EK QP))
    (λ {A} {B} {f} {x} {y} qf → (flow qf , encode qf))

forgetQuoteFlow
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (WithPort {ℓ} {ℓRel} {ℓCode})
      (Flow2Cat.WithPort {ℓ} {ℓRel} {ℓCode})
forgetQuoteFlow {ℓ} {ℓRel} {ℓCode} =
  PortStack.forgetPort (flowPort {ℓ} {ℓRel} {ℓCode})
    ∘F forgetQuoteFlowEncode {ℓ} {ℓRel} {ℓCode}

forgetQuoteEncode
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (WithPort {ℓ} {ℓRel} {ℓCode})
      (Encode2Cat.WithPort {ℓ} {ℓRel} {ℓCode})
forgetQuoteEncode {ℓ} {ℓRel} {ℓCode} =
  PortStack.forgetPort (encodePort {ℓ} {ℓRel} {ℓCode})
    ∘F forgetQuoteFlowEncode {ℓ} {ℓRel} {ℓCode}
