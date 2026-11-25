import OAI.LinearAlgebra.MatrixExponent.AdjacentDuplicates
import OAI.LinearAlgebra.MatrixExponent.Batcher
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.BitonicMerge

/-! # Initial exact network for element distinctness -/

namespace OAI.LinearAlgebra.MatrixExponent

/-- Each bit of each record of each list occupies a separate exterior position. -/
theorem wd_lists (w t : ℕ) : wd (lists w t) = t * listBits w := by
  induction t with
  | zero => simp [wd]
  | succ t ih =>
    change wd (tree w (word (2 * w))) + wd (lists w t) = _
    rw [wd_tree, wd_word, ih]
    unfold listBits
    ring

variable (F : Type) [Field F]

private theorem pin {a : Wire} {f : Val a → Bool} {m : ℕ} (h : DNet F a .bit f m) :
    ∃ v ≤ m + 1, Net F a .unit (fun x _ => if f x = true then 1 else 0) v := by
  obtain ⟨v, hv, h⟩ := h
  refine ⟨v + 1, Nat.add_le_add_right hv 1, ?_⟩
  have ht := Net.table (F := F) .bit .unit (fun b _ => if b = true then 1 else 0) (by decide)
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using h.comp ht

/-- Sorting preserves the multiset. On the result, strict inequalities
between adjacent words characterize distinctness. -/
private theorem seed_size (w : ℕ) (hw : 1 ≤ w) :
    ∃ m, Realizes F w 1 m ∧ m ≤ 2000 * listBits w * w ^ 2 := by
  have sort := sortTree_net (compare_exchange F (2 * w)) w
  have test := adjacent_net (compare_lt F (2 * w)) w
  obtain ⟨v, hv, h⟩ := pin F (sort.comp test)
  refine ⟨v + listBits w, ⟨v, ?_, by simp⟩, ?_⟩
  · have ok (x : Val (tree w (word (2 * w)))) :
        adjacent w (sortTree w x) = true ↔ (flatten w x).Nodup :=
      (adjacent_iff _ _ (sortTree_sorted w x)).trans (sortTree_perm w x).nodup_iff
    simpa only [distinctPower, mul_one, ok] using h.pre (.unit _)
  · refine (Nat.add_le_add_right hv _).trans ?_
    rw [wd_word]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0)
    unfold listBits
    rw [Nat.succ_eq_add_one, pow_succ 2 j]
    have hp : 0 < 2 ^ j := by positivity
    ring_nf
    omega

theorem seed : Seed (Realizes F) := by
  refine ⟨2000, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with w hw
  obtain ⟨m, h, hm⟩ := seed_size F w hw
  exact ⟨m, h, by exact_mod_cast hm⟩

end OAI.LinearAlgebra.MatrixExponent
