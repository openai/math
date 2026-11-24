import OAI.Computability.VPVNP.RAMSortLayers
import Mathlib.Data.List.OfFn

/-!
# Row-major indices for grouped transcript records

The initial record array of Lemma 10.1 has one fixed-width block per group.
Flattening those blocks reads the global array in increasing address order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

variable {α : Type*}

/-- Reading consecutive aligned blocks enumerates exactly the entries of the large block. -/
theorem flatten_ofFn_blocks (h d : ℕ) (x : ℕ → α) :
    (List.ofFn fun v : Fin (2 ^ d) ↦ List.ofFn (block h v.val x)).flatten =
      List.ofFn (block (h + d) 0 x) := by
  have hs : 2 ^ (h + d) = 2 ^ d * 2 ^ h := by rw [Nat.add_comm, Nat.pow_add]
  rw [List.ofFn_congr hs, List.ofFn_mul]
  simp only [block, Nat.zero_mul, Nat.zero_add]
  rfl

/-- Look up a slot in the flattened array by its group index and within-group offset. -/
theorem getElem?_flatten_rect {rows : List (List α)} {W : ℕ}
    (hw : ∀ r ∈ rows, r.length = W) {v j : ℕ} (hv : v < rows.length) (hj : j < W) :
    rows.flatten[v * W + j]? = rows[v][j]? := by
  induction rows generalizing v with
  | nil => simp at hv
  | cons r rows ih =>
    have hr : r.length = W := hw r (by simp)
    cases v with
    | zero =>
      simpa only [List.flatten_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero] using
        (List.getElem?_append_left (l₁ := r) (l₂ := rows.flatten) (i := j) (hr ▸ hj))
    | succ v =>
      have hv' : v < rows.length := by simpa using hv
      simp only [List.flatten_cons, List.getElem_cons_succ, Nat.succ_mul]
      rw [List.getElem?_append_right (by omega), hr]
      rw [show v * W + W + j - W = v * W + j by omega]
      exact ih (fun t ht ↦ hw t (List.mem_cons_of_mem _ ht)) hv'

end RAMSort

end VPVNP
end Computability
end OAI
