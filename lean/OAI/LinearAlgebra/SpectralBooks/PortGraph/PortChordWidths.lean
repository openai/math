import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementClass

/-! # Collecting parallel port-graph wires into chord widths -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace PortGraph

noncomputable section

open SiteTensor ChordGraph
open scoped BigOperators Classical

variable {k : ℕ} {E : Type} [Fintype E] (G : PortGraph (Fin k) E)

/-- Sort the two endpoints of a non-loop edge. A loop has both ends at one
site, so its entire tensor is a local vector. -/
def chordWidth (e : E) (w : ℕ) : Widths k :=
  if h : G.tail e < G.head e then Finsupp.single ⟨(G.tail e, G.head e),h⟩ w
  else if h' : G.head e < G.tail e then Finsupp.single ⟨(G.head e, G.tail e),h'⟩ w
  else 0

/-- The integer width of each unoriented chord, summed over parallel edges. -/
def chordWidths (w : E → ℕ) : Widths k := ∑ e, G.chordWidth e (w e)

theorem total_chordWidths_le (w : E → ℕ) : total (G.chordWidths w) ≤ ∑ e, w e := by
  simp only [chordWidths, map_sum]
  apply Finset.sum_le_sum
  intro e _
  unfold chordWidth
  split_ifs <;> simp

theorem load_chordWidths_le (w : E → ℕ) (i : Fin k) :
    load i (G.chordWidths w) ≤ ∑ p : G.Port i, w p.1.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : E × Bool => G.vertex p.1 p.2 = i))
    (by simp) (fun p => w p.1), Finset.sum_filter, Fintype.sum_prod_type]
  simp only [chordWidths, map_sum]
  apply Finset.sum_le_sum
  intro e _
  simp only [Fintype.sum_bool, vertex, chordWidth]
  split_ifs <;> simp_all [load_single, add_mul, eq_comm]
  omega

variable [Nonempty (Fin k)] (F : Type*) [Field F]

private theorem wireClass_loop (i : Fin k) :
    ofRaw ((Raw.diagonal (Fin 2) F (Fin 2)).group ![i,i]) = 1 := by
  let T := Raw.diagonal (Fin 2) F (Fin 2)
  have he : (![i,i] : Fin 2 → _) = fun _ => i := by funext j; fin_cases j <;> rfl
  rw [he]
  apply le_antisymm (ofRaw_le_iff.mpr (T.group_const_restricts_one _))
  apply one_le_of_ne_zero
  rw [ne_eq, ofRaw_eq_zero_iff]
  apply (T.group_ne_zero_iff _).mpr
  intro hz
  have h := congrFun hz (fun _ => (0 : Fin 2))
  change (Raw.diagonal (Fin 2) F (Fin 2)).coeff (fun _ => (0 : Fin 2)) = 0 at h
  simp only [Raw.diagonal_coeff_at (0 : Fin 2), forall_const, ↓reduceIte, one_ne_zero] at h

omit [Fintype E] in
private theorem edgeRaw_chordWidth (e : E) (w : E → ℕ) :
    graphClass F (G.chordWidth e (w e)) = ofRaw (G.edgeRaw F (fun j => Fin (2 ^ w j)) e) := by
  rw [edgeRaw, ofRaw_group_diagonal_fin_pow]
  unfold chordWidth
  split_ifs with h h'
  · rw [graphClass_single]; rfl
  · rw [graphClass_single]
    exact congrArg (· ^ w e) (ofRaw_eq_iff.mpr (Raw.grouped_wire_symm F (Fin 2) (G.head e) (G.tail e)))
  · have he : G.tail e = G.head e := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
    rw [he, wireClass_loop, graphClass_zero, one_pow]

/-- Reorienting edges, packing parallel wire words together, and removing
self-loops gives exactly the class of the original equality tensor. -/
theorem ofRaw_rawWiring_eq_graphClass (w : E → ℕ) :
    ofRaw (G.rawWiring F (fun e => Fin (2 ^ w e))) = graphClass F (G.chordWidths w) := by
  rw [ofRaw_rawWiring, chordWidths]
  have h (s : Finset E) :
      graphClass F (∑ e ∈ s, G.chordWidth e (w e)) = ∏ e ∈ s, ofRaw (G.edgeRaw F (fun j => Fin (2 ^ w j)) e) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert e s he ih =>
      simp only [Finset.sum_insert he, graphClass_add, Finset.prod_insert he, ih, edgeRaw_chordWidth]
  exact (h Finset.univ).symm

end
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
