import OAI.Computability.BorderVNP.DiagonalTallyReportAllocation

/-! # Word bounds for the native report controls -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace DiagonalTallyAllocation

/-- The reference and operand reservations for one cell contain the gadget
bits and the gadget-coordinate words counted by control 16. -/
theorem AfterTasks.stride_le_localBase (a : AfterTasks) (cells : 0 < a.bound.cells) :
    1 + a.bound.gadgets*(1+a.bound.countWidth) ≤ a.localBase := by
  have one := Nat.le_mul_of_pos_left a.bound.gadgets cells
  have bits := Nat.mul_le_mul_right a.bound.countWidth one
  rw [localBase, a.footprint]
  simp only [Bounds.operands, Nat.mul_add, Nat.mul_one]
  omega

/-- The before-task control addresses fit below the physical limit.
Control 16 takes its count stride from the same layout as the post-task bank. -/
theorem BeforeTasks.controls_fit {w : ℕ} (a : BeforeTasks) (post : AfterTasks)
    (bounds : post.bound = a.bound) (cells : 0 < a.bound.cells)
    (beforeFits : a.limit < 2^w) (postFits : post.localBase < 2^w)
    (previous : ℕ → ℕ) (prevFits : ∀ i < 37, previous i < 2^w) :
    ∀ i < 37, a.controls previous i < 2^w := by
  have supplement := Nat.le_mul_of_pos_left a.bound.supplementStride cells
  have stride : a.bound.supplementStride < 2^w := by
    rw [a.footprint] at beforeFits
    omega
  have digit := post.stride_le_localBase (bounds.symm ▸ cells)
  rw [bounds] at digit
  unfold BeforeTasks.limit BeforeTasks.bundleTable BeforeTasks.ranges BeforeTasks.six BeforeTasks.four
    BeforeTasks.merged BeforeTasks.counters BeforeTasks.supplement at beforeFits
  intro i hi
  unfold BeforeTasks.controls
  split <;> first
    | exact prevFits _ hi
    | exact stride
    | exact digit.trans_lt postFits
    | omega
    | (simp only [BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four,
        BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement]; omega)

/-- The post-task pointer fields and gadget count fit the allocated post-task
bank, while the two scanner format words and count bit width fit their types. -/
theorem AfterTasks.controls_fit {w : ℕ} (a : AfterTasks)
    (cells : 0 < a.bound.cells) (count : a.bound.countWidth ≤ w) {fieldWidth bodyCap : ℕ}
    (fieldFits : fieldWidth < 2^w) (bodyFits : bodyCap < 2^w) (postFits : a.localBase < 2^w)
    (previous : ℕ → ℕ) (prevFits : ∀ i < 37, previous i < 2^w) :
    ∀ i < 37, a.controls fieldWidth bodyCap previous i < 2^w := by
  have countFits : a.bound.countWidth < 2^w := count.trans_lt Nat.lt_two_pow_self
  have gadgetsFit : a.bound.gadgets < 2^w := by
    have stride := a.stride_le_localBase cells
    have gadget := Nat.le_mul_of_pos_right a.bound.gadgets (by omega : 0 < 1+a.bound.countWidth)
    omega
  unfold AfterTasks.localBase AfterTasks.fresh AfterTasks.descriptors AfterTasks.refs at postFits
  intro i hi
  unfold AfterTasks.controls
  split <;> first
    | exact prevFits _ hi
    | exact fieldFits
    | exact bodyFits
    | exact countFits
    | exact gadgetsFit
    | omega
    | (simp only [AfterTasks.refs]; omega)

end DiagonalTallyAllocation

end BorderVNP
end Computability
end OAI
