import OAI.Hierarchy.ProtocolRAMTurnEdgeData
import OAI.Hierarchy.ProtocolRAMVisitAdjacency
import OAI.Hierarchy.TaggedWireEndpointVisits

namespace OAI
/-! # The two physical sites used by the native scan on each true CT occurrence -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnEdges

open AdaptiveProbe ProbeStage CoreBoard WordSeats WireTelescope SettledMatrix VisitOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAMTurnGeometry
open scoped Classical

variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K)

local notation "L" => B.matrixLayout inj pad

theorem canonical_length (s : ProtocolRAMTurnGeometry.Source edges h d k) :
    ((L).steps s).length=ProtocolRAMTurnGeometry.length s := by
  rcases s with e|i|c
  · rfl
  · change (oriented _ _ (B.ordinary i)).length=_
    unfold oriented
    split <;> simpa only [List.length_reverse] using length_ordinary B i
  · change (oriented _ _ (B.centers c)).length=_
    unfold oriented
    split <;> simpa only [List.length_reverse] using length_center B c

private theorem physical (e : Edges S h d k) :
    Between (ends B inj pad (B.row e))
      ((place (CoreBoard.ends π e).1).val) ((place (CoreBoard.ends π e).2).val) := by
  rcases B.core_order inj pad e with ⟨x,y⟩|⟨x,y⟩
  · exact .inl ⟨congrArg Fin.val x,congrArg Fin.val y⟩
  · exact .inr ⟨congrArg Fin.val y,congrArg Fin.val x⟩

theorem steps (s : ProtocolRAMTurnGeometry.Source edges h d k) :
    Steps (ends B inj pad) (visit B inj pad s) 0 (walk B s) := by
  rcases s with e|i|c
  · intro j hj
    change j < [e].length at hj
    have eq : j=0 := by simpa using hj
    subst j
    exact .inl ⟨rfl,rfl⟩
  · exact (commodity_steps (S:=S) π i).map (fun s=>(place s).val) B.row (physical B inj pad)
  · exact (reserve_steps (S:=S) π c).map (fun s=>(place s).val) B.row (physical B inj pad)

theorem adjacent {n : ℕ} (items : Fin n ≃ ProtocolRAMTurnGeometry.Source edges h d k)
    (origin : Fin n → ℕ) (paid : ℕ → Fin edges)
    (read : ∀a j (h : j < (walk B (items a)).length),paid (origin a+j)=(walk B (items a))[j])
    (i : Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMTurnGeometry.length ∘ items)))
    (h : 0 < (ProtocolRAMTurnOrder.raw (ProtocolRAMTurnGeometry.length ∘ items) i).2.val) :
    let len := ProtocolRAMTurnGeometry.length ∘ items
    let row := ProtocolRAMTurnOrder.raw len i
    let e := ends B inj pad (paid (origin row.1+(row.2.val-1)))
    let site := ProtocolRAMVisitAdjacency.vertex len (fun a=>visit B inj pad (items a))
    e.1+e.2 = site i+site ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩ :=
  ProtocolRAMVisitAdjacency.adjacent (ProtocolRAMTurnGeometry.length ∘ items) origin
    (fun a=>visit B inj pad (items a)) (fun a=>walk B (items a)) (ends B inj pad) paid
    (fun a=>walk_length B (items a)) read (fun a=>steps B inj pad (items a)) i h

end Hierarchy.ProtocolRAMTurnEdges

namespace Hierarchy.ProtocolRAMTurnStepOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix
variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K)
local notation "L" => B.matrixLayout inj pad

def reverse : ProtocolRAMTurnGeometry.Source edges h d k → Bool
  | .inl _ => false
  | .inr (.inl i) => decide (¬(L).goods.tail i < (L).goods.head i)
  | .inr (.inr c) => decide (¬(L).reserve.tail c < (L).reserve.head c)

end Hierarchy.ProtocolRAMTurnStepOrder

end
end OAI
