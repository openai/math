import OAI.Hierarchy.ConnectedCut
import OAI.Hierarchy.OrthogonalCutLoad

namespace OAI
/-! # The prescribed load on every block of a connected graph -/

namespace Hierarchy.IncidenceGraph

open scoped Classical BigOperators

variable (G : IncidenceGraph)

theorem prescribed_block_load (connected : ∀ u v, G.Connected u v)
    {J : Type} [Fintype J] [Nontrivial J] (π : G.V → J) (onto : Function.Surjective π)
    (j : J) {w : ℝ} (hw : 0 ≤ w) :
    w ≤ ‖∑ i : {p : G.E × Bool // π (G.portOwner p) = j}, w • G.orthogonalSite i.val‖ := by
  classical
  let S := Finset.univ.filter fun v : G.V => π v = j
  have cut := G.boundary_nonempty_of_block connected π onto j
  have cardinal : 1 ≤ (G.boundaryEdges S).card := Finset.card_pos.mpr cut
  have norm := G.norm_orthogonal_cut S hw
  have equal :
      (∑ i : {p : G.E × Bool // π (G.portOwner p) = j}, w • G.orthogonalSite i.val) =
        ∑ i ∈ Finset.univ.filter (fun i : G.E × Bool => G.portOwner i ∈ S), w • G.orthogonalSite i := by
    symm
    apply Finset.sum_subtype
    intro i
    simp [S]
  rw [equal, norm]
  calc
    w = w * Real.sqrt 1 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast cardinal)) hw

theorem prescribed_partition_load (connected : ∀ u v, G.Connected u v)
    {J : Type} [Fintype J] [Nontrivial J] (π : G.V → J) (onto : Function.Surjective π)
    {w : ℝ} (hw : 0 ≤ w) :
    Fintype.card J * w ≤ ∑ j : J,
      ‖∑ i : {p : G.E × Bool // π (G.portOwner p) = j}, w • G.orthogonalSite i.val‖ := by
  classical
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset J))
    (fun j _ => G.prescribed_block_load connected π onto j hw)


end Hierarchy.IncidenceGraph

end OAI
