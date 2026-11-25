import OAI.Computability.BorderVNP.PackedInheritedNamedWidthRead
import OAI.Computability.BorderVNP.PackedInheritedWorkNames
import OAI.Computability.BorderVNP.PackedHistoryPrivateNamedRows
import OAI.Computability.BorderVNP.PackedNamedPortHeaders

/-! # The fixed work-augmented inner compiler on the actual named schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows Shortening.PublicParallel
open Shortening.PublicEndpoints Packing Packing.Inherited Packing.Inherited.WorkWords InheritedBank NamedKernel Physical
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u
variable {D m b k np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, src.Node last high V E w k i}
variable (r : src.NamedRun last high V E w cap keep hk nodes)

local notation3 "Seeds" i => Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (Fin.val i+1))
local notation3 "Words" j => WithWidths (src.StatePins last high V E w j) (V j) w
local notation3 "Pins" => Pin (Cube D) (fun i => (src.pattern i).bins.Bin) (src.asPath.depth last high) e.count (fun _ => w)
local notation3 "At" j => NamedState.Admissible (src.NamedGood last high V E w cap keep) j
variable (header : WorkWords.Ports np) (leaf : P ↪ Fin np)
variable (rect : ∀ i : Fin b, V (i.val+1) = siteCapacity e (k*V i.val) (Fintype.card
    (Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (i.val+1)))))
variable (fits : ∀ i : Fin b, V (i.val+1) ≤ 2^w)

/-- Static seed code chosen before the scheduler's children and guesses. -/
noncomputable abbrev widthSeed (i : Fin b) : (Seeds i) ≃ Fin (Fintype.card (Seeds i)) :=
  r.directorySeed i

/-- Native work kernel before the schedule's histogram coordinate reindexing. -/
noncomputable def widthNode (i : Fin b) : Frame (LocalPins k (Words i.val) ((Seeds i) × Fin e.count × Fin w))
    (Result (Words (i.val+1))) :=
  jointAt (n := Fintype.card (Seeds i)) (A := Seeds i) (Old := src.StatePins last high V E w i.val)
    (B := Cover.AddressCircuit.ProductSlots (Fintype.card (Cube D)) (src.asPath.depth last high (i.val+1)+1) ⊕ ↥(src.catalog (i.val+1)))
    (V := V i.val) (V' := V (i.val+1)) (E := E (i.val+1)) (k := k) (w := w) e (r.widthSeed i).toEmbedding (header.nested k V i.val) (rect i) (fits i) (nodes i)

/-- Gate family used by the inner physical tree. Profile wires are reindexed
in precisely the order of the normalized program's own codec. -/
noncomputable def widthSteps : Steps k b (fun j => Words j) Pins :=
  fun j hj => scheduled (r.widthNode header rect fits ⟨j,hj⟩)
    (pinEquiv (I := Cube D) (B := fun i => (src.pattern i).bins.Bin) (depth := src.asPath.depth last high)
      (e := e) (fun _ => w) ⟨j,hj⟩) id


end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
