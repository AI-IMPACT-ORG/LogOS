{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PacksThreading where

-- Smoke test: the “LogicCore + domain bundle” threading is available directly
-- from the application pack claims.

open import LogOS.Prelude

open import LogOS.API.Assumptions.Core using (LogicCore)
import LogOS.Packs.Assumptions.ZFC as AssumpZFC
import LogOS.Packs.Assumptions.Universality as AssumpUni

import LogOS.Packs.Agents.All as PacksAgents
import LogOS.Packs.Agents.Experimental.All as PacksAgentsExp
import LogOS.Packs.InfoTheory.All as PacksInfo
import LogOS.Packs.Opacity.Experimental.All as PacksOpacityExp
import LogOS.Packs.Complexity.Experimental.All as PacksComplexityExp
import LogOS.Packs.UniversalIR.All as PacksUIR
import LogOS.Packs.Universality.All as PacksUniversality
import LogOS.Packs.ZFC.All as PacksZFC

import LogOS.Packs.ZFC.WFGraph as WF
import LogOS.Packs.UniversalIR.Kernel as UIRK

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)

import LogOS.Packs.Agents.Socket.Core as AgentSock
import LogOS.Packs.Agents.Socket.FromLogicCore as AgentSockFromCore
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)

-- Pack entrypoints re-export coherent assumption bundles.

AgentsBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
AgentsBundle C = PacksAgents.AssumptionBundles.UniversalityBundle C

AgentsExperimentalUniBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
AgentsExperimentalUniBundle C = PacksAgentsExp.AssumptionBundles.UniversalityBundle C

AgentsExperimentalPhysBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
AgentsExperimentalPhysBundle C = PacksAgentsExp.AssumptionBundles.PhysicsOfInformationBundle C

InfoTheoryBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
InfoTheoryBundle C = PacksInfo.AssumptionBundles.PhysicsOfInformationBundle C

OpacityBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
OpacityBundle C = PacksOpacityExp.AssumptionBundles.ZFBundle C

ComplexityBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
ComplexityBundle C = PacksComplexityExp.AssumptionBundles.PhysicsOfInformationBundle C

UniversalIRBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
UniversalIRBundle C = PacksUIR.AssumptionBundles.UniversalityBundle C

UniversalityBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
UniversalityBundle C = PacksUniversality.AssumptionBundles.UniversalityBundle C

ZFCBundle : ∀ {ℓ : Level} → LogicCore {ℓ} → Set _
ZFCBundle C = PacksZFC.AssumptionBundles.ZFCBundle C

-- ZFC/WFGraph: Full layer.

core-Full
  : ∀ {ℓ : Level} {A : WF.Full.Assumptions {ℓ}}
  → WF.Full.Claim A → LogicCore {ℓ}
core-Full = WF.Full.Claim.core

zfBundle-Full
  : ∀ {ℓ : Level} {A : WF.Full.Assumptions {ℓ}}
    (C : WF.Full.Claim A)
  → AssumpZFC.ZFBundle (WF.Full.Claim.core C)
zfBundle-Full = WF.Full.Claim.zfBundle

-- ZFC/WFGraph: Textbook ZFC layer.

core-TextbookZFC
  : ∀ {ℓ : Level} {A : WF.TextbookZFC.Assumptions {ℓ}}
  → WF.TextbookZFC.Claim A → LogicCore {ℓ}
core-TextbookZFC = WF.TextbookZFC.Claim.core

zfcBundle-TextbookZFC
  : ∀ {ℓ : Level} {A : WF.TextbookZFC.Assumptions {ℓ}}
    (C : WF.TextbookZFC.Claim A)
  → AssumpZFC.ZFCBundle (WF.TextbookZFC.Claim.core C)
zfcBundle-TextbookZFC = WF.TextbookZFC.Claim.zfcBundle

-- UniversalIR kernel instance: threaded Universality assumptions.

core-UniversalIRKernel : LogicCore {lzero}
core-UniversalIRKernel = UIRK.core

universality-UniversalIRKernel : AssumpUni.UniversalityBundle core-UniversalIRKernel
universality-UniversalIRKernel = UIRK.universality

-- Agents socket exposes the derived LogicCore projection and a LogicCore-first constructor.

core-AgentSocket
  : ∀ {ℓ ℓTask : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {Task : Set ℓTask}
  → AgentSock.AgentSocket Sig Q Task
  → LogicCore {ℓ}
core-AgentSocket = AgentSock.AgentSocket.core

module _ {ℓ ℓTask : Level} (C : LogicCore {ℓ}) (Task : Set ℓTask) where
  open AgentSockFromCore.For C Task using (mkCodeSocket; mkBoundarySocket)

-- Opacity GRH/ZFC bridge projects the shared core + ZF bundle.

coreLK-ZFCFlowStability
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q} {RS : RiemannSpectral}
  → PacksOpacityExp.Applications.GRH.Guardless.ZFCBridge.ZFCFlowStability K RS → LogicCore {ℓ}
coreLK-ZFCFlowStability = PacksOpacityExp.Applications.GRH.Guardless.ZFCBridge.ZFCFlowStability.coreLK

zfBundle-ZFCFlowStability
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q} {RS : RiemannSpectral}
  → (Stab : PacksOpacityExp.Applications.GRH.Guardless.ZFCBridge.ZFCFlowStability K RS)
  → AssumpZFC.ZFBundle (PacksOpacityExp.Applications.GRH.Guardless.ZFCBridge.ZFCFlowStability.coreLK Stab)
zfBundle-ZFCFlowStability = PacksOpacityExp.Applications.GRH.Guardless.ZFC.zfBundleFromStability
