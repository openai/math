import OAI.Computability.NearSquareRoot.SynchronizedNumberedBits
import OAI.Computability.NearSquareRoot.CoprimeBox

/-! # The physical block widths used by the synchronized permutation schedule

The blocks partition the original padded axis fields once the box has at least four
axes. Bounds refer to every bit of a grouped address, including padding. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open SynchronizedBlocks

variable {k L : ℕ} {box : List (ℕ × ℕ)}

/-- Four to seven axis fields contribute to each grouped physical address. -/
theorem physicalWidth_le_seven (hb : BoxShape.Valid k L box) (j : Fin (box.length / 4)) :
    physicalWidth (box := box) j ≤ 7 * L :=
  bitWidth_le (fun i => (box.get i).1)
    (fun i => (hb.axisBounds _ (List.get_mem box i)).2.1) j

theorem four_le_physicalWidth (hb : BoxShape.Valid k L box) (j : Fin (box.length / 4)) :
    4 ≤ physicalWidth (box := box) j := by
  calc
    4 ≤ count j := (count_bounds j).1
    _ = ∑ _i : Fin (count j), 1 := by simp
    _ ≤ physicalWidth (box := box) j := Finset.sum_le_sum fun i _ =>
      (hb.axisBounds _ (List.get_mem box (axis j i))).1

/-- Grouping preserves the total number of address bits. -/
theorem sum_physicalWidth (hb : BoxShape.Valid k L box) (hd : 4 ≤ box.length) :
    ∑ j : Fin (box.length / 4), physicalWidth (box := box) j = k := by
  let w (i : Fin box.length) := (box.get i).1
  calc
    _ = ∑ p : Σ j : Fin (box.length/4), Fin (count j), w (axis p.1 p.2) :=
      (Fintype.sum_sigma fun p : Σ j : Fin (box.length/4), Fin (count j) => w (axis p.1 p.2)).symm
    _ = ∑ i : Fin box.length, w i := (coordinates hd).sum_comp w
    _ = k := (Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum

theorem sum_physicalWidth_le (hb : BoxShape.Valid k L box) :
    ∑ j : Fin (box.length / 4), physicalWidth (box := box) j ≤ k := by
  by_cases hd : 4 ≤ box.length
  · exact (sum_physicalWidth hb hd).le
  · have count_zero : box.length / 4 = 0 := by omega
    have : IsEmpty (Fin (box.length/4)) := ⟨fun i => by have := i.isLt; omega⟩
    simp

theorem blockCount_le (hb : BoxShape.Valid k L box) : box.length / 4 ≤ k := by
  have := hb.axisCount
  have := Nat.div_le_self k L
  omega

/-- The concrete box has axis fields of twenty binary logarithms and at most seven
fields per block. -/
theorem physicalWidth_log (hb : BoxShape.Valid k (BoxScale.width k) box)
    (j : Fin (box.length / 4)) : physicalWidth (box := box) j ≤ 140 * Nat.clog 2 k := by
  simpa [BoxScale.width, ← Nat.mul_assoc] using physicalWidth_le_seven hb j

/-- The full enumeration used by a local Beneš or routing table has polynomial
length in the address width, including any borrowed fibers. -/
theorem physicalVolume_poly (hb : BoxShape.Valid k (BoxScale.width k) box) (hk : 1 < k)
    (j : Fin (box.length / 4)) :
    2 ^ physicalWidth (box := box) j ≤ (2*k)^140 := by
  calc
    _ ≤ 2^(7*BoxScale.width k) := Nat.pow_le_pow_right (by decide) (physicalWidth_le_seven hb j)
    _ = (BoxScale.span k)^7 := by rw [BoxScale.span, ← Nat.pow_mul, Nat.mul_comm]
    _ ≤ ((2*k)^20)^7 := Nat.pow_le_pow_left (BoxScale.span_le hk) _
    _ = _ := by rw [← Nat.pow_mul]

/-- Total number of rows in one family of local permutation tables. -/
theorem sum_physicalVolume_poly (hb : BoxShape.Valid k (BoxScale.width k) box) (hk : 1 < k) :
    (∑ j : Fin (box.length / 4), 2 ^ physicalWidth (box := box) j) ≤ k * (2*k)^140 := by
  calc
    _ ≤ ∑ _j : Fin (box.length / 4), (2*k)^140 := Finset.sum_le_sum fun j _ =>
      physicalVolume_poly hb hk j
    _ = (box.length / 4) * (2*k)^140 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (blockCount_le hb)

/-- The executable box constructor eventually partitions all `k` bits into
blocks with logarithmic widths and a polynomial total table size. -/
theorem eventually_physicalShape : ∃ K : ℕ, ∀ k ≥ K,
    let box := CoprimeBox.box k
    (∑ j : Fin (box.length / 4), physicalWidth (box := box) j) = k ∧
    (∀ j : Fin (box.length / 4), physicalWidth (box := box) j ≤ 140 * Nat.clog 2 k) ∧
    (∑ j : Fin (box.length / 4), 2 ^ physicalWidth (box := box) j) ≤ k * (2*k)^140 := by
  obtain ⟨K,valid⟩ := CoprimeBox.eventually_valid
  refine ⟨max K 1024,fun k hk => ?_⟩
  have hb := valid k ((le_max_left ..).trans hk)
  have hk' : 1024 ≤ k := (le_max_right ..).trans hk
  have hd := four_le_length hb (three_width_lt hk')
  exact ⟨sum_physicalWidth hb hd, physicalWidth_log hb, sum_physicalVolume_poly hb (by omega)⟩

end BoxFin

end NearSquareRoot
end Computability
end OAI
