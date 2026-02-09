{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Safety.ArchitectureFromSafety where

-- Architecture from safety: assuming only the kernel interface (no extra
-- paradox-enabling axioms), the boundary/port/interlingua spine is forced.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port

import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Ports.Semantic.CanonicalPorts as Canonical
import LogOS.Theorems.Meta.Bootstrapping as Bootstrapping
import LogOS.Theorems.Meta.Safety.DesignChoice as DesignChoice

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  where

  module BS = Bootstrapping.For K
  module CP = Canonical.For K
  open CP using (B; CodePort; BoundaryPort∂)
  -- Avoid name clashes with record fields; refer to BS.bootstrap-iso explicitly.

  guard-decode-core
    : ∀ γ → Kernel.decode K (Kernel.Guard K γ)
        ≡ GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K)) (Kernel.decode K γ)
  guard-decode-core = Kernel.guard-decode K

  decode∘encode-core : ∀ c → Kernel.decode K (Kernel.encode K c) ≡ c
  decode∘encode-core = Kernel.decode∘encode K

  forced-translation
    : ∀ {ℓForm₁ ℓForm₂ : Level}
      (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
      (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
      (A  : Interop.PortAdapter B P₁ P₂)
    → Interop.For.Adapter≈ B P₁ P₂ A (Interop.For.canonicalAdapter B P₁ P₂)
  forced-translation P₁ P₂ A =
    let module I = Interop.For B P₁ P₂
    in I.adapter-unique A

  bootstrap-unique-core
    : ∀ (A : Interop.PortAdapter B CodePort BoundaryPort∂)
    → Interop.For.Adapter≈ B CodePort BoundaryPort∂ A BS.bootstrap
  bootstrap-unique-core A =
    let module I = Interop.For B CodePort BoundaryPort∂
    in I.adapter-unique A

  record Architecture : Set (lsuc (lsuc ℓ)) where
    field
      boundary   : BoundaryIO Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
      codePort   : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B
      boundaryPort : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B
      bootstrap    : Interop.PortAdapter B codePort boundaryPort
      bootstrap-unique
        : ∀ (A : Interop.PortAdapter B codePort boundaryPort)
        → Interop.For.Adapter≈ B codePort boundaryPort A bootstrap
      bootstrap-iso : BS.BootstrapIso codePort boundaryPort
      guard-decode  : ∀ γ → Kernel.decode K (Kernel.Guard K γ)
                       ≡ GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K)) (Kernel.decode K γ)
      decode∘encode : ∀ c → Kernel.decode K (Kernel.encode K c) ≡ c

  architecture : Architecture
  architecture =
    record
      { boundary = B
      ; codePort = CodePort
      ; boundaryPort = BoundaryPort∂
      ; bootstrap = BS.bootstrap
      ; bootstrap-unique = bootstrap-unique-core
      ; bootstrap-iso = BS.bootstrap-iso
      ; guard-decode = guard-decode-core
      ; decode∘encode = decode∘encode-core
      }

module FromDesignChoice
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (D : DesignChoice.DesignChoice Sig Q)
  where
  open DesignChoice.DesignChoice D using (K)
  module A = For K
  open A public using (Architecture; architecture; forced-translation)
