import OAI.Computability.BorderVNP.PackedScanSpec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic

/-! # Weighted requests in a sorted key table

Source rows sort before every query row of their key. Query rows have weight
zero, so the run total at each query equals the entire fiber sum, even when
several queries read the same key.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram

/-- Sum of every input record at one dynamic address. -/
def bucket {N : ℕ} (key weight : Fin N → ℕ) (address : ℕ) : ℕ :=
  ∑ u : Fin N, if key u = address then weight u else 0

/-- Reordering records cannot affect their per-address total. -/
theorem bucket_perm {N : ℕ} (key weight : Fin N → ℕ) (π : Equiv.Perm (Fin N)) (a : ℕ) :
    bucket (key ∘ π) (weight ∘ π) a = bucket key weight a :=
  Equiv.sum_comp π (fun u => if key u = a then weight u else 0)

/-- Sort-key order implies address order, since the low tag is a single bit. -/
theorem key_mono {N : ℕ} (key : Fin N → ℕ) (tag : Fin N → Bool)
    (sorted : Monotone fun i => 2*key i + (tag i).toNat) : Monotone key := by
  intro i j hij
  have h := sorted hij
  change 2*key i + (tag i).toNat ≤ 2*key j + (tag j).toNat at h
  cases hi : tag i <;> cases hj : tag j <;> simp [hi, hj] at h <;> omega

/-- Sorted nonnegative prefix sums cannot exceed the full bin. -/
theorem segment_le_bucket {N : ℕ} (key weight : ℕ → ℕ)
    (sorted : Monotone fun i : Fin N => key i.val) (j : Fin N) :
    PackedScan.segmentTotal key weight j.val ≤ bucket (fun i : Fin N => key i.val)
      (fun i => weight i.val) (key j.val) := by
  rw [PackedScan.total_eq_sum key weight j.val (fun u v huv hv => sorted
    (show (⟨u, by omega⟩ : Fin N) ≤ ⟨v, by omega⟩ from huv)),
    bucket, Fin.sum_univ_eq_sum_range (fun u => if key u = key j.val then weight u else 0)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono j.isLt)

/-- All same-key sources occur by the time the scan reaches a query. Later queries
have zero weight. Thus a single prefix scan supplies all repeated reads. -/
theorem segment_eq_bucket {N : ℕ} (key weight : ℕ → ℕ) (tag : Fin N → Bool)
    (sorted : Monotone fun i : Fin N => 2*key i.val + (tag i).toNat)
    (query_zero : ∀ i, tag i = true → weight i.val = 0)
    (j : Fin N) (hj : tag j = true) :
    PackedScan.segmentTotal key weight j.val = bucket (fun i : Fin N => key i.val)
      (fun i => weight i.val) (key j.val) := by
  have hs := key_mono (fun i : Fin N => key i.val) tag sorted
  rw [PackedScan.total_eq_sum key weight j.val (fun u v huv hv => hs
    (show (⟨u, by omega⟩ : Fin N) ≤ ⟨v, by omega⟩ from huv)),
    bucket, Fin.sum_univ_eq_sum_range (fun u => if key u = key j.val then weight u else 0)]
  apply Finset.sum_subset (Finset.range_mono j.isLt)
  intro i hi hbefore
  by_cases he : key i = key j.val
  · rw [ite_eq_left he]
    let l : Fin N := ⟨i, Finset.mem_range.mp hi⟩
    have hlj : j ≤ l := by
      change j.val ≤ i
      have := Finset.mem_range.not.mp hbefore
      omega
    have h := sorted hlj
    change 2 * key j.val + (tag j).toNat ≤ 2 * key i + (tag l).toNat at h
    rw [he, hj, Bool.toNat_true] at h
    apply query_zero l
    cases hc : tag l
    · simp [hc] at h
    · rfl
  · exact ite_eq_right he

end PackedHistogram

end BorderVNP
end Computability
end OAI
