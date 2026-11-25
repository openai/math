import OAI.Hierarchy.ABPFirstCutAvoid
import OAI.Hierarchy.GraphContractions
import Mathlib.Data.Fintype.Powerset

namespace OAI
/-! # Prefix cuts forced by graph cutwidth -/

namespace Hierarchy.IncidenceGraph

open scoped Classical

noncomputable section

variable (G : IncidenceGraph)

/-- Edges crossing the bipartition `S | Sᶜ`. -/
def boundaryEdges (S : Finset G.V) : Finset G.E :=
  Finset.univ.filter fun e => ¬(G.left e ∈ S ↔ G.right e ∈ S)

@[simp] theorem boundaryEdges_empty : G.boundaryEdges ∅ = ∅ := by
  ext e
  simp [boundaryEdges]

@[simp] theorem boundaryEdges_univ : G.boundaryEdges Finset.univ = ∅ := by
  ext e
  simp [boundaryEdges]

/-- All vertex sets with more than `b` crossing edges. -/
def cutFamily (b : ℕ) : Finset (Finset G.V) :=
  Finset.univ.filter fun S => b < (G.boundaryEdges S).card

@[simp] theorem mem_cutFamily {S : Finset G.V} {b : ℕ} :
    S ∈ G.cutFamily b ↔ b < (G.boundaryEdges S).card := by simp [cutFamily]

@[simp] theorem empty_notMem_cutFamily (b : ℕ) : ∅ ∉ G.cutFamily b := by simp

@[simp] theorem univ_notMem_cutFamily (b : ℕ) : Finset.univ ∉ G.cutFamily b := by simp

theorem card_cutFamily_le (b : ℕ) : (G.cutFamily b).card ≤ 2 ^ Fintype.card G.V := by
  simpa only [Fintype.card_finset] using (G.cutFamily b).card_le_univ

theorem boundaryEdges_rankPrefix (ord : G.V ≃ Fin (Fintype.card G.V)) (k : ℕ) :
    G.boundaryEdges (Finset.univ.filter fun v : G.V => (ord v).val < k) = G.cutEdges ord k := by
  ext e
  simp [boundaryEdges, cutEdges]

/-- Failure of a cutwidth bound forces every vertex order to visit the wide-cut family. -/
theorem hitsEveryOrder_cutFamily {b : ℕ} (h : ¬ G.CutwidthAtMost b) :
    ABPFirstCut.HitsEveryOrder (G.cutFamily b) := by
  apply ABPFirstCut.hitsEveryOrder_of_equiv
  intro ord
  by_contra! missing
  apply h
  refine ⟨ord, fun k => ?_⟩
  simpa [boundaryEdges_rankPrefix] using missing k

theorem card_cutFamily_pos {b : ℕ} (h : ¬ G.CutwidthAtMost b) : 0 < (G.cutFamily b).card :=
  Finset.card_pos.mpr (G.hitsEveryOrder_cutFamily h).nonempty

end

end Hierarchy.IncidenceGraph

end OAI
