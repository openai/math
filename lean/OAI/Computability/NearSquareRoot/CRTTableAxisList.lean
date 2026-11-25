import OAI.Computability.IntegerMultiplication.Code.Slice
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.OfFn

/-! # Contiguous lists of CRT axes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

/-- Serializing the moduli of a contiguous node agrees with slicing the
globally serialized moduli at the node's first position. -/
theorem axisSlice {d : ℕ} (a : Fin d → ℕ) (js : List (Fin d)) (base : ℕ)
    (hpos : ∀ k (hk : k < js.length), js[k].val = base + k) :
    js.map (fun j => tally (a j)) =
      ((List.ofFn (fun j => tally (a j))).drop base).take js.length := by
  have hlen : js.length ≤ d - base := by
    by_cases he : js.length = 0
    · omega
    have hk : js.length - 1 < js.length := by omega
    have hb := js[js.length - 1].isLt
    rw [hpos _ hk] at hb
    omega
  apply List.ext_getElem
  · simp [Nat.min_eq_left hlen]
  · intro k hk h'
    rw [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    exact congrArg (fun j => tally (a j)) (Fin.ext (hpos k (by simpa using hk)))

/-- The rows before a pivot are exactly the axes with smaller global index. -/
theorem axisPrefix {d : ℕ} (js : List (Fin d)) (base : ℕ)
    (hpos : ∀ k (hk : k < js.length), js[k].val = base + k) (i : Fin js.length) :
    (js.take i.val).toFinset = js.toFinset.filter (· < js[i.val]) := by
  ext j
  simp only [List.mem_toFinset, Finset.mem_filter]
  constructor
  · intro hj
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hj
    rw [List.getElem_take]
    have hki : k < i.val := by simpa [Nat.min_eq_left i.isLt.le] using hk
    refine ⟨List.getElem_mem _, ?_⟩
    apply Fin.lt_def.mpr
    rw [hpos, hpos]
    omega
  · rintro ⟨hj, hi⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hj
    have hki : k < i.val := by
      change js[k].val < js[i.val].val at hi
      rwa [hpos, hpos, Nat.add_lt_add_iff_left] at hi
    have ht : k < (js.take i.val).length := by simp [hki]
    simpa only [List.getElem_take] using (List.getElem_mem ht)

end CRTTable

end NearSquareRoot
end Computability
end OAI
