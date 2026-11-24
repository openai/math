import OAI.Computability.VPVNP.CompletionReplacement
import OAI.Computability.VPVNP.GrassmannFrameDimensions

/-!
# The quadrilateral of a completion-column move

In the equality argument of Lemma 5.3, replace one column of the common
completion by a vector outside the entire frame. The two original planes
and the two new planes form a square of types `r` and one. The sums across
the move use both the old and the new column, so their dimensions can be
read off from the extended independent frame.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set Submodule Function

private theorem sup_completedBlock_replacement {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] {s : ℕ} (v : ι → V) (w : Fin s → V) (i : Fin s) (x : V) (S T : Set ι) :
    completedBlock (K := K) v w S ⊔ completedBlock v (update w i x) T =
      completedBlock v (Fin.snoc w x) S ⊔ completedBlock v (Fin.snoc w x) T := by
  unfold completedBlock
  rw [sup_sup_sup_comm, span_completion_sup_replacement, ← sup_sup_distrib_left]

/-- The old left, old right, new right, and new left completed blocks have
dimension `m`. In this cyclic order they form an `(r, 1)` square. -/
theorem completion_move_square {m r s : ℕ} {v : Fin (r + r) → Space m}
    {w : Fin s → Space m} {x : Space m} (hm : s + r = m) (i : Fin s)
    (h : LinearIndependent (ZMod 2) (Sum.elim v (Fin.snoc w x))) :
    ∃ a b c d : Plane m,
      a.val = completedBlock v w (leftIndices r) ∧
      b.val = completedBlock v w (rightIndices r) ∧
      c.val = completedBlock v (update w i x) (rightIndices r) ∧
      d.val = completedBlock v (update w i x) (leftIndices r) ∧ IsSquare r 1 a b c d := by
  have ho := independent_completion_init h
  have hn := independent_completion_replacement i h
  refine ⟨leftPlane v w hm ho, rightPlane v w hm ho, rightPlane v _ hm hn,
    leftPlane v _ hm hn, rfl, rfl, rfl, rfl, ?_⟩
  let dim (U : Submodule (ZMod 2) (Space m)) := Module.finrank (ZMod 2) U
  let L {k : ℕ} (t : Fin k → Space m) := completedBlock (K := ZMod 2) v t (leftIndices r)
  let R {k : ℕ} (t : Fin k → Space m) := completedBlock (K := ZMod 2) v t (rightIndices r)
  constructor
  · exact hasType_framePlanes v w hm ho
  · change dim (R w ⊔ R (update w i x)) = _
    rw [sup_completedBlock_replacement, sup_idem]
    exact (finrank_rightBlock v _ h).trans (by omega)
  · change dim (R (update w i x) ⊔ L (update w i x)) = _
    rw [sup_comm]
    exact (finrank_sup_frameBlocks v _ hn).trans (by omega)
  · change dim (L (update w i x) ⊔ L w) = _
    rw [sup_comm, sup_completedBlock_replacement, sup_idem]
    exact (finrank_leftBlock v _ h).trans (by omega)
  · change dim (L w ⊔ R (update w i x)) = _
    rw [sup_completedBlock_replacement]
    exact (finrank_sup_frameBlocks v _ h).trans (by omega)
  · change dim (R w ⊔ L (update w i x)) = _
    rw [sup_completedBlock_replacement, sup_comm]
    exact (finrank_sup_frameBlocks v _ h).trans (by omega)

end Grassmann

end VPVNP
end Computability
end OAI
