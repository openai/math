import OAI.Computability.BorderVNP.DiagonalExternalFragmentHostWords
import Mathlib.Order.Preorder.Finite

/-! # The common physical rank of a crossing edge in every native team's scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

/-- Every increasing enumeration of the same physical addresses gives the
same dense rank to each occupied edge, including the empty rectangle. -/
theorem ordered_rows_unique {E : Type*} {M K : ℕ} (o p : E ≃ Fin M) (r s : Fin M ↪o Fin K)
    (atEdge : ∀ e, r (o e) = s (p e)) : o = p ∧ r = s := by
  let f := o.symm.trans p
  have atRank (i : Fin M) : r i = s (f i) := by simpa [f] using atEdge (o.symm i)
  have mono : StrictMono f := fun i j h => s.lt_iff_lt.mp ((atRank i).symm ▸ (atRank j).symm ▸ r.strictMono h)
  have same := mono.eq_id
  constructor
  · apply Equiv.ext
    intro e
    have hit := congrFun same (o e)
    simpa [f] using hit.symm
  · apply RelEmbedding.ext
    intro i
    simpa only [congrFun same i, id_eq] using atRank i

/-- Use one chosen increasing physical numbering in all team-specific native
host readbacks, preserving every team's individual intermediate memory. -/
theorem common_ordered_rows {E Team : Type*} [Fintype E] {K : ℕ} (addr : E ↪ Fin K)
    (check : Team → (E ≃ Fin (Fintype.card E)) → (Fin (Fintype.card E) ↪o Fin K) → Prop)
    (found : ∀ t, ∃ o r, (∀ e, r (o e) = addr e) ∧ check t o r) :
    ∃ o r, (∀ e, r (o e) = addr e) ∧ ∀ t, check t o r := by
  obtain ⟨o,r,hr⟩ := exists_ordered_rows addr
  refine ⟨o,r,hr,?_⟩
  intro t
  obtain ⟨p,s,hs,checked⟩ := found t
  obtain ⟨rfl,rfl⟩ := ordered_rows_unique o p r s fun e => (hr e).trans (hs e).symm
  exact checked

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
