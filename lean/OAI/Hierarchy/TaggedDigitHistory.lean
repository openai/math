import OAI.Hierarchy.TaggedDigitValues
import OAI.Hierarchy.TaggedRadixOrder
import OAI.Hierarchy.TaggedSortedKeys
import OAI.Hierarchy.TaggedStableObservations

namespace OAI
/-! # Refining the numerical key from digit observations of canonical words -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork SortedBlock
open scoped Classical
noncomputable section

variable {h k : ℕ}

def allowed {n h : ℕ} (x : (Fin n × Fin (RadixRecord.width h)) → Bool) :=
  ∀ i, RadixRecord.Canonical h (fun b => x (i,b))

theorem blank_real (h : ℕ) : RadixRecord.blank h (RadixRecord.real h) = false := by
  simp [RadixRecord.blank,RadixRecord.real,RadixRecord.dummy]
theorem blank_dummy (h : ℕ) : RadixRecord.blank h (RadixRecord.dummy h) = true := by simp [RadixRecord.blank]
theorem blank_zero (h : ℕ) : RadixRecord.blank h (RadixRecord.zero h) = false := by
  simp [RadixRecord.blank,RadixRecord.zero,RadixRecord.dummy]

private theorem zero_of_member {n : ℕ} (x : (Fin n × Fin (RadixRecord.width h)) → Bool) (ok : allowed x)
    {z} (hz : z ∈ RadixRecord.realWords h x) : z (RadixRecord.zero h) = false := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hz).1
  rcases ok i with eq | ⟨_,_,zero⟩
  · exact (congrFun eq _).trans (blank_zero h)
  · exact zero

def orderedAt (h k i : ℕ) {n : ℕ} (x : (Fin n × Fin (RadixRecord.width h)) → Bool) :=
  (RadixRecord.realWords h x).Pairwise (fun a b => RadixRecord.keyValue a%(2^k)^i ≤ RadixRecord.keyValue b%(2^k)^i)

theorem refine_digit {m n : ℕ} (i : ℕ)
    (x : (Fin m × Fin (RadixRecord.width h)) → Bool) (y : (Fin n × Fin (RadixRecord.width h)) → Bool)
    (ok : allowed y) (prev : orderedAt h k i x)
    (tick : (RadixRecord.realWords h y).Pairwise (fun a b => readKey (RadixRecord.digit h k i) a ≤ readKey (RadixRecord.digit h k i) b) ∧
      ∀a,bucket (readKey (RadixRecord.digit h k i)) a (RadixRecord.realWords h y) =
        bucket (readKey (RadixRecord.digit h k i)) a (RadixRecord.realWords h x)) :
    (RadixRecord.realWords h y).Perm (RadixRecord.realWords h x) ∧ orderedAt h k (i+1) y := by
  let d := RadixRecord.digit h k i
  have upper := refine_list_order (readKey d) (fun z => RadixRecord.keyValue z%(2^k)^i) prev tick.1 tick.2
  refine ⟨perm_of_buckets _ tick.2, List.Pairwise.imp_of_mem (p := upper) ?_⟩
  intro a b ha hb pair
  rw [show readKey d a = RadixRecord.keyValue a/(2^k)^i%2^k from RadixRecord.digit_value a (zero_of_member _ ok ha) k i,
    show readKey d b = RadixRecord.keyValue b/(2^k)^i%2^k from RadixRecord.digit_value b (zero_of_member _ ok hb) k i] at pair
  rw [pow_succ,Nat.mod_mul,Nat.mod_mul]
  exact (field_le (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))).mpr pair

theorem ordered_cover {m : ℕ} (n : ℕ) (cover : h+1 ≤ (n+1)*k)
    (y : (Fin m × Fin (RadixRecord.width h)) → Bool) (ordered : orderedAt h k (n+1) y) :
    ((RadixRecord.realWords h y).map RadixRecord.keyValue).Pairwise (·≤·) := by
  have covered (z : Bits (RadixRecord.width h)) : RadixRecord.keyValue z < (2^k)^(n+1) := by
    rw [←pow_mul,Nat.mul_comm k]
    exact (RadixRecord.keyValue_lt z).trans_le (Nat.pow_le_pow_right (by decide) cover)
  apply List.pairwise_map.mpr
  simpa only [orderedAt,Nat.mod_eq_of_lt (covered _)] using ordered

end
end Hierarchy.Tagged.Radix

end OAI
