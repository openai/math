import OAI.Hierarchy.TaggedShorterBudget

namespace OAI
/-! # Padding and splitting positive-width links into actual lane words -/

noncomputable section
namespace Hierarchy.TaggedShorterFields
open TaggedShorterBudget

/-- A lane reads its own consecutive field. Only the final high bits can be
padding; every repeated use of the same site gets its own lane. -/
def slice {bits : ℕ} (width : ℕ) (x : Fin bits → Bool) (k : ℕ) (j : Fin width) : Bool :=
  if h : k*width+j.val < bits then x ⟨k*width+j.val,h⟩ else false

theorem eq_iff_slices {bits width count : ℕ} (room : bits ≤ count*width)
    (x y : Fin bits → Bool) :
    (∀ k : Fin count, slice width x k.val = slice width y k.val) ↔ x = y := by
  constructor
  · intro eqn
    funext i
    have pos : 0 < width := by
      by_contra! hz
      have : width = 0 := by omega
      simp [this] at room
      have := i.isLt
      omega
    have hq : i.val / width < count := (Nat.div_lt_iff_lt_mul pos).mpr (i.isLt.trans_le room)
    let k : Fin count := ⟨i.val / width,hq⟩
    let j : Fin width := ⟨i.val % width,Nat.mod_lt _ pos⟩
    have reconstruct : k.val*width+j.val=i.val := by
      simpa [k,j,Nat.mul_comm] using Nat.div_add_mod i.val width
    simpa [slice,reconstruct,i.isLt] using congrFun (eqn k) j
  · rintro rfl k
    rfl

/-- The real normalized width used in the pruning bill provides enough
integer wires after dyadic rounding, also at widths zero and exactly one. -/
theorem rounded_room (bits w m : ℕ) (hw : 0<w) :
    let y := (bits:ℝ)/w
    let Y := dyadic (widthIndex m y)
    bits ≤ copies y * ⌈Y*w⌉₊ := by
  intro y Y
  have hw' : 0 < (w:ℝ) := by exact_mod_cast hw
  have exactWidth : y*w=bits := div_mul_cancel₀ _ hw'.ne'
  have hy : 0≤y := div_nonneg (Nat.cast_nonneg _) hw'.le
  by_cases hb : bits = 0
  · simp [hb]
  have pos : 0<y := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)) hw'
  have num : 1≤copies y := by
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr pos)
  have rounded := Nat.le_ceil (Y*w)
  by_cases narrow : y≤1
  · have Ylo : y≤Y := by simpa only [min_eq_left narrow] using (widthIndex_spec m (y:=y)).2
    have b : (bits:ℝ) ≤ ⌈Y*w⌉₊ := by
      calc
        _ = y*w := exactWidth.symm
        _ ≤ Y*w := mul_le_mul_of_nonneg_right Ylo hw'.le
        _ ≤ _ := rounded
    exact (show bits≤⌈Y*w⌉₊ by exact_mod_cast b).trans (Nat.le_mul_of_pos_left _ num)
  · have Yone : Y=1 := by simp [Y,widthIndex,narrow,dyadic]
    rw [Yone,one_mul,Nat.ceil_natCast]
    have count := Nat.le_ceil y
    have b : (bits:ℝ) ≤ (copies y:ℝ)*w := by
      calc
        _ = y*w := exactWidth.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right count hw'.le
    exact_mod_cast b

end Hierarchy.TaggedShorterFields

end
end OAI
