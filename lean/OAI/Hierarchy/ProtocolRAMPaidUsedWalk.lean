import OAI.Hierarchy.ProtocolRAMTurnDictionary

namespace OAI
/-! # Every traversed native edge of a live original row has positive reported width -/

noncomputable section
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix
open ProtocolRAM.Calendar CoreRoute
open LinearAlgebra.SpectralBooks ChordGraph

variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K)

private theorem walk_mem (src : ProtocolRAMTurnGeometry.Source edges h d k) (e : Fin edges) :
    e ∈ ProtocolRAMTurnEdges.walk B src → e ∈ (B.matrixLayout inj pad).steps src := by
  intro mem
  rcases src with i | i | c
  · exact mem
  · change e ∈ B.ordinary i at mem
    change e ∈ oriented _ _ (B.ordinary i)
    unfold oriented
    split <;> simpa using mem
  · change e ∈ B.centers c at mem
    change e ∈ oriented _ _ (B.centers c)
    unfold oriented
    split <;> simpa using mem

/-- Positivity on the oriented matrix walk carries over to the raw-order
occurrence dictionary, including repeated uses of a single physical edge. -/
theorem used_in_walk (o : Orders h d k) (width : Fin edges → ℕ)
    (src : ProtocolRAMTurnGeometry.Source edges h d k)
    (live : ∀ t : Fin ((B.matrixLayout inj pad).steps src).length,
      0 < width (((B.matrixLayout inj pad).steps src).get t))
    (j : ℕ) (hj : j < ProtocolRAMTurnGeometry.length src) :
    ∃ e : Fin edges, e.val = ProtocolRAMTurnOccurrence.edgeAt B inj pad o
      (ProtocolRAMTurnGeometry.origin o src+j) ∧ 0 < width e := by
  have bound : j < (ProtocolRAMTurnEdges.walk B src).length := by
    rwa [ProtocolRAMTurnEdges.walk_length]
  let e := (ProtocolRAMTurnEdges.walk B src)[j]'bound
  have member : e ∈ (B.matrixLayout inj pad).steps src :=
    walk_mem B inj pad src e (List.getElem_mem bound)
  obtain ⟨t,et⟩ := List.mem_iff_get.mp member
  exact ⟨e,(ProtocolRAMTurnOccurrence.read B inj pad o src j bound).symm,et ▸ live t⟩

end Hierarchy.ProtocolRAMPaidTurnPlacement

end
end OAI
