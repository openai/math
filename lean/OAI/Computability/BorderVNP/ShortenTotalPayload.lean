import OAI.Computability.BorderVNP.ShortenEpochRoundRecordTree

/-! # Total scalar payload from the measured local record counts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Finset
open scoped BigOperators Classical

variable {D : ℕ} {P T : Type*} [Fintype P] [Fintype T] {bits : P → ℕ}
    {N : Network D P bits}

/-- Each box's scalar payload is charged by the expanded records in its
actual host tile. The sum over the physical sites is at most the number of
tiles times the measured per-tile record ceiling. -/
theorem payload_sum_le_tiles (prior payload : N.Site → ℕ) (address : N.Site → T) (cap : ℕ)
    (measured : ∀ t, localRecords N true prior payload (fun v => address v = t) ≤ cap) :
    ∑ v, payload v ≤ Fintype.card T * cap := by
  classical
  have tile (t : T) : (∑ v : {v : N.Site // address v = t}, payload v.val) ≤ cap := by
    have boxes : testedWidth payload (fun v => address v = t) ≤
        testedWidth (fun v => boxCost true (prior v) (payload v)) (fun v => address v = t) := by
      unfold testedWidth
      apply Finset.sum_le_sum
      intro v _
      split
      · simp [boxCost, recordCost]
        omega
      · simp
    have loc := measured t
    unfold localRecords at loc
    have ht : testedWidth payload (fun v => address v = t) ≤ cap := by omega
    unfold testedWidth at ht
    rw [←Finset.sum_filter] at ht
    have eq := Finset.sum_subtype (F := inferInstance) (p := fun v : N.Site => address v = t)
      (Finset.univ.filter (fun v => address v = t)) (fun v => by simp) payload
    exact eq ▸ ht
  rw [←Fintype.sum_fiberwise address payload]
  calc
    _ ≤ ∑ _ : T, cap := Finset.sum_le_sum fun t _ => tile t
    _ = _ := by simp

end Shortening

end BorderVNP
end Computability
end OAI
