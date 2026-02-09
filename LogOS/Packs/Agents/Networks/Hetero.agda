{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Hetero where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPreorder; MonoMap)
open import LogOS.Minimal.Adjunction using (MonoidalOps)
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; satSystem)
open import LogOS.Ports.Semantic.SatMor using (SatMor; SatHom)
open import LogOS.Minimal.ConAlg using (ConAlg)
import LogOS.Minimal.Thin2Cat as Thin2Cat
import LogOS.Minimal.RelPreorder as RP
import LogOS.Minimal.RelThin2Cat as RelThin2Cat

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Kernel as LK

-- Heterogeneous agent networks: each role may carry its own signature/kernel.
-- Wiring is expressed via satisfaction morphisms between boundary interfaces.
--
-- `Edge` uses `SatMor`, which preserves *and reflects* satisfaction. This makes
-- the edge a conservative translation rather than a one-way sound abstraction.
-- Use `EdgeSound` for sound-only (one-way) translations.

record AgentNode {ℓ ℓTask : Level} : Set (lsuc (lsuc (ℓ ⊔ ℓTask))) where
  field
    Sig  : LogOSSignature ℓ
    Q    : QAdapter ℓ
    Task : Set ℓTask
    Sock : AgentSocket Sig Q Task

  -- Re-export the socket surface for convenience.
  open AgentSocket Sock public

record AgentNetwork {ℓ ℓTask ℓRole : Level} (Role : Set ℓRole)
  : Set (lsuc (lsuc (ℓ ⊔ ℓTask ⊔ ℓRole))) where

  field
    node : Role → AgentNode {ℓ} {ℓTask}

  -- Per-role accessors.
  Sig : Role → LogOSSignature ℓ
  Sig r = AgentNode.Sig (node r)

  Q : Role → QAdapter ℓ
  Q r = AgentNode.Q (node r)

  Task : Role → Set ℓTask
  Task r = AgentNode.Task (node r)

  Sock : (r : Role) → AgentSocket (Sig r) (Q r) (Task r)
  Sock r = AgentNode.Sock (node r)

  -- Boundary interface per role.
  Ctx : Role → Set ℓ
  Ctx r = LogOSSignature.∂Cosp (Sig r)

  Con : Role → Set ℓ
  Con r = let open AgentSocket (Sock r) in Con_bnd

  Sat : (r : Role) → Ctx r → Con r → Set ℓ
  Sat r = BoundaryIO.Sat∂ (AgentSocket.boundaryIO (Sock r))

  -- Boundary-facing system per role (Ctx/Con/Sat).

  BoundarySystemAt : Role → SatSystem {ℓCtx = ℓ} {ℓCon = ℓ} {ℓSat = ℓ}
  BoundarySystemAt r =
    satSystem (Ctx r) (Con r) (Sat r)

  conAlg : (r : Role) → ConAlg {ℓ}
  conAlg r = AgentSocket.conAlg (Sock r)

  tensorAt : (r : Role) → Con r → Con r → Con r
  tensorAt r c d = ConAlg._⊗∂_ (conAlg r) c d

  -- Boundary preorder per role.
  ConPreorderAt : Role → ConPreorder ℓ
  ConPreorderAt r = BulkBoundary.bnd (LK.Kernel.BB (AgentSocket.LK (Sock r)))

  -- A policy is a role-indexed assignment of boundary constraints.
  Policy : Set (ℓ ⊔ ℓRole)
  Policy = (r : Role) → Con r

  -- Policies induced by the per-socket contract semantics.
  SafetyPolicy : Policy
  SafetyPolicy r = AgentSocket.SafetySem (Sock r)

  ObjectivePolicy : Policy
  ObjectivePolicy r = AgentSocket.ObjectiveSem (Sock r)

  AssumesPolicy : Policy
  AssumesPolicy r = AgentSocket.AssumesSem (Sock r)

  -- Policy preorder (pointwise).
  Policy≤ : Policy → Policy → Set (ℓ ⊔ ℓRole)
  Policy≤ pol pol' = ∀ r → AgentSocket._⊑bnd_ (Sock r) (pol r) (pol' r)

  PolicyPreorder : ConPreorder (ℓ ⊔ ℓRole)
  PolicyPreorder =
    record
      { Con = Policy
      ; _⊑_ = Policy≤
      ; refl = λ {pol} r → ConPreorder.refl (ConPreorderAt r)
      ; trans = λ {pol} {pol'} {pol''} le₁ le₂ r →
          ConPreorder.trans (ConPreorderAt r) (le₁ r) (le₂ r)
      }

  -- Edge wiring: a conservative translation between boundary satisfactions.
  record Edge (r s : Role) : Set (lsuc (ℓ ⊔ ℓRole)) where
    field
      satMor : SatMor (BoundarySystemAt r) (BoundarySystemAt s)

    translateCon : Con r → Con s
    translateCon = SatMor.mapCon satMor

  -- Sound-only edge wiring (no reflection assumption).
  record EdgeSound (r s : Role) : Set (lsuc (ℓ ⊔ ℓRole)) where
    field
      satHom : SatHom (BoundarySystemAt r) (BoundarySystemAt s)

    translateCon : Con r → Con s
    translateCon = SatHom.mapCon satHom

  -- Locally preordered 2-category of monotone maps between role boundary preorders.
  record MonoHom (r s : Role) : Set (lsuc (ℓ ⊔ ℓRole)) where
    field
      fn   : Con r → Con s
      mono : MonoMap (ConPreorderAt r) (ConPreorderAt s) fn

  -- Pointwise refinement between monotone maps.
  --
  -- This is the primitive 2-cell notion; mutual refinement (`≈`) is derived.
  infix 4 _⊑MH_
  _⊑MH_ : ∀ {r s} → MonoHom r s → MonoHom r s → Set ℓ
  _⊑MH_ {s = s} f g =
    ∀ c → ConPreorder._⊑_ (ConPreorderAt s) (MonoHom.fn f c) (MonoHom.fn g c)

  MonoHomPreorder : Role → Role → ConPreorder (lsuc (ℓ ⊔ ℓRole))
  MonoHomPreorder r s =
    record
      { Con = MonoHom r s
      ; _⊑_ = λ f g →
          Lift (lsuc (ℓ ⊔ ℓRole))
            (f ⊑MH g)
      ; refl = λ {f} →
          lift (λ c → ConPreorder.refl (ConPreorderAt s))
      ; trans = λ {f} {g} {h} fg gh →
          lift (λ c → ConPreorder.trans (ConPreorderAt s) (Lift.lower fg c) (Lift.lower gh c))
      }

  -- RelPreorder-enriched 2-category of monotone maps (no `Lift` needed).

  MonoHomRelPreorder : Role → Role → RP.RelPreorder (lsuc (ℓ ⊔ ℓRole)) ℓ
  MonoHomRelPreorder r s =
    record
      { Con = MonoHom r s
      ; _⊑_ = _⊑MH_
      ; refl = λ {f} c → ConPreorder.refl (ConPreorderAt s)
      ; trans = λ {f} {g} {h} fg gh c →
          ConPreorder.trans (ConPreorderAt s) (fg c) (gh c)
      }

  monoComp : ∀ {r s t} → MonoHom s t → MonoHom r s → MonoHom r t
  monoComp g f =
    record
      { fn = λ c → MonoHom.fn g (MonoHom.fn f c)
      ; mono = λ p → MonoHom.mono g (MonoHom.mono f p)
      }

  MonoThin2Cat : Thin2Cat.Thin2Cat ℓRole (lsuc (ℓ ⊔ ℓRole))
  MonoThin2Cat =
    record
      { Obj = Role
      ; Hom = MonoHomPreorder
      ; id  = λ {r} →
          record
            { fn = λ c → c
            ; mono = λ p → p
            }
      ; _∘_ = λ {r} {s} {t} g f → monoComp g f
      ; comp-mono-l = λ {r} {s} {t} {f} {f'} {g} fg →
          lift (λ c → Lift.lower fg (MonoHom.fn g c))
      ; comp-mono-r = λ {r} {s} {t} {f} {g} {g'} gg' →
          lift (λ c → MonoHom.mono f (Lift.lower gg' c))
      }

  MonoRelThin2Cat : RelThin2Cat.RelThin2Cat ℓRole (lsuc (ℓ ⊔ ℓRole)) ℓ
  MonoRelThin2Cat =
    record
      { Obj = Role
      ; Hom = MonoHomRelPreorder
      ; id  = λ {r} →
          record
            { fn = λ c → c
            ; mono = λ p → p
            }
      ; _∘_ = λ {r} {s} {t} g f → monoComp g f
      ; comp-mono-l = λ {r} {s} {t} {f} {f'} {g} fg →
          (λ c → fg (MonoHom.fn g c))
      ; comp-mono-r = λ {r} {s} {t} {f} {g} {g'} gg' →
          (λ c → MonoHom.mono f (gg' c))
      }

  edgeTensor : ∀ {r s} → Edge r s → Con s → Con r → Con s
  edgeTensor {r} {s} e cₛ cᵣ =
    tensorAt s cₛ (Edge.translateCon e cᵣ)

  edgeUpdate : ∀ {r s} → Edge r s → Policy → Con s
  edgeUpdate {r} {s} e pol = edgeTensor e (pol s) (pol r)

  edgeTensorSound : ∀ {r s} → EdgeSound r s → Con s → Con r → Con s
  edgeTensorSound {r} {s} e cₛ cᵣ =
    tensorAt s cₛ (EdgeSound.translateCon e cᵣ)

  edgeUpdateSound : ∀ {r s} → EdgeSound r s → Policy → Con s
  edgeUpdateSound {r} {s} e pol = edgeTensorSound e (pol s) (pol r)

  -- Monotone edge translation (an extra assumption when needed).
  EdgeMono : ∀ {r s} (e : Edge r s) → Set ℓ
  EdgeMono {r} {s} e = MonoMap (ConPreorderAt r) (ConPreorderAt s) (Edge.translateCon e)

  edgeMonoHom : ∀ {r s} (e : Edge r s) → EdgeMono e → MonoHom r s
  edgeMonoHom e monoE =
    record
      { fn = Edge.translateCon e
      ; mono = monoE
      }

  tensorMono : (r : Role) → Con r → MonoHom r r
  tensorMono r c =
    let
      module MB = MonoidalOps (ConAlg.MBnd (conAlg r))
      CP = ConPreorderAt r
    in
    record
      { fn = λ d → tensorAt r c d
      ; mono = λ {x} {y} x≤y →
          MB.mono⊗ (ConPreorder.refl CP {c = c}) x≤y
      }

  edgeTensor-mono-right
    : ∀ {r s} (e : Edge r s)
    → EdgeMono e
    → (cₛ : Con s)
    → ∀ {cᵣ cᵣ'}
    → AgentSocket._⊑bnd_ (Sock r) cᵣ cᵣ'
    → AgentSocket._⊑bnd_ (Sock s) (edgeTensor e cₛ cᵣ) (edgeTensor e cₛ cᵣ')
  edgeTensor-mono-right {r} {s} e monoE cₛ c≤c' =
    let
      map = monoComp (tensorMono s cₛ) (edgeMonoHom e monoE)
    in
    MonoHom.mono map c≤c'

  edgeTensor-mono
    : ∀ {r s} (e : Edge r s)
    → EdgeMono e
    → ∀ {cₛ cₛ' cᵣ cᵣ'}
    → AgentSocket._⊑bnd_ (Sock s) cₛ cₛ'
    → AgentSocket._⊑bnd_ (Sock r) cᵣ cᵣ'
    → AgentSocket._⊑bnd_ (Sock s) (edgeTensor e cₛ cᵣ) (edgeTensor e cₛ' cᵣ')
  edgeTensor-mono {r} {s} e monoE {cₛ} {cₛ'} {cᵣ} {cᵣ'} c≤c' d≤d' =
    let
      module MB = MonoidalOps (ConAlg.MBnd (conAlg s))
      CP = ConPreorderAt s
      step₁ = edgeTensor-mono-right e monoE cₛ d≤d'
      step₂ = MB.mono⊗ c≤c' (ConPreorder.refl CP {c = Edge.translateCon e cᵣ'})
    in
    ConPreorder.trans CP step₁ step₂

  edgeUpdate-mono
    : ∀ {r s} (e : Edge r s)
    → EdgeMono e
    → ∀ {pol pol'}
    → Policy≤ pol pol'
    → AgentSocket._⊑bnd_ (Sock s) (edgeUpdate e pol) (edgeUpdate e pol')
  edgeUpdate-mono {r} {s} e monoE pol≤pol' =
    edgeTensor-mono {r = r} {s = s} e monoE (pol≤pol' s) (pol≤pol' r)

  edgeUpdate-monoMap
    : ∀ {r s} (e : Edge r s)
    → EdgeMono e
    → MonoMap PolicyPreorder (ConPreorderAt s) (edgeUpdate e)
  edgeUpdate-monoMap e monoE pol≤pol' =
    edgeUpdate-mono e monoE pol≤pol'
