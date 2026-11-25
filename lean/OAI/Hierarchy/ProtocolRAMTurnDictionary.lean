import OAI.Hierarchy.ProtocolRAMTurnEdgeData
import OAI.Hierarchy.TaggedWireCoreLayout
import OAI.Hierarchy.TaggedWireNativeOrder

namespace OAI
/-! # Fixed and live paid-edge words in original occurrence order -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnOccurrence
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix
open ProtocolRAM.Calendar CoreRoute
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor

variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)

local notation "L" => B.matrixLayout inj pad
local notation "Count" => Fintype.card (Slots h d k)

/-- The value outside the occurrence bank is immaterial, including when it is empty. -/
def edgeAt (j : ℕ) : ℕ :=
  if hj : j < edges+Count then ((L).nativeEdge (enum B o) ⟨j,hj⟩).val else 0

theorem permanent (e : Fin edges) : edgeAt B inj pad o e.val=e.val := by
  have fit : e.val < edges+Count := by have := e.isLt;omega
  rw [edgeAt,dite_eq_left fit]
  change ((L).nativeEdge (enum B o) (Fin.castAdd Count e)).val=e.val
  simp [Layout.nativeEdge]; rfl

theorem liveSlot (v : Slots h d k) :
    edgeAt B inj pad o (edges+(slotOrder o v).val)=(RouteOccurrence.edge (toOccurrence B v)).val := by
  have fit : edges+(slotOrder o v).val<edges+Count := Nat.add_lt_add_left (slotOrder o v).isLt _
  rw [edgeAt,dite_eq_left fit]
  change ((L).nativeEdge (enum B o) (Fin.natAdd edges (slotOrder o v))).val=_
  simp [Layout.nativeEdge,enum]
  change ((toOccurrence B ((slotOrder o).symm ((slotOrder o) v))).edge).val = _
  rw [Equiv.symm_apply_apply]

theorem address (s : ProtocolRAMTurnGeometry.Source edges h d k) (j : ℕ)
    (hj : j < ProtocolRAMTurnGeometry.length s) :
    ProtocolRAMTurnGeometry.origin o s+j < edges+Count := by
  rcases s with e|i|c
  · have eq : j=0 := by change j<1 at hj;omega
    subst j
    change e.val+0 < edges+Count
    have := e.isLt
    omega
  · let t : Fin (arity i) := ⟨j,hj⟩
    rw [show ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inl i))+j =
      edges+(slotOrder o (.inl ⟨i,t⟩)).val from ProtocolRAMTurnGeometry.goods_at o i t]
    exact Nat.add_lt_add_left (slotOrder o (.inl ⟨i,t⟩)).isLt _
  · let t : Fin 2 := ⟨j,hj⟩
    rw [show ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inr c))+j =
      edges+(slotOrder o (.inr ⟨c,t⟩)).val from ProtocolRAMTurnGeometry.center_at o c t]
    exact Nat.add_lt_add_left (slotOrder o (.inr ⟨c,t⟩)).isLt _

theorem read (s : ProtocolRAMTurnGeometry.Source edges h d k) (j : ℕ)
    (hj : j < (ProtocolRAMTurnEdges.walk B s).length) :
    edgeAt B inj pad o (ProtocolRAMTurnGeometry.origin o s+j)=
      ((ProtocolRAMTurnEdges.walk B s)[j]).val := by
  rcases s with e|i|c
  · change j < [e].length at hj
    have eq : j=0 := by simpa using hj
    subst j
    exact permanent B inj pad o e
  · have b : j < arity i := hj.trans_le (ProtocolRAMTurnGeometry.length_ordinary B i).le
    let t : Fin (arity i) := ⟨j,b⟩
    rw [show ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inl i))+j=
        edges+(slotOrder o (.inl ⟨i,t⟩)).val from ProtocolRAMTurnGeometry.goods_at o i t,
      liveSlot]
    rfl
  · have b : j < 2 := hj.trans_le (ProtocolRAMTurnGeometry.length_center B c).le
    let t : Fin 2 := ⟨j,b⟩
    rw [show ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inr c))+j=
        edges+(slotOrder o (.inr ⟨c,t⟩)).val from ProtocolRAMTurnGeometry.center_at o c t,
      liveSlot]
    rfl

end Hierarchy.ProtocolRAMTurnOccurrence

end
end OAI
