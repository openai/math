import OAI.Optimization.LinearProgramming.Compression.ProxyRangeMachine
import OAI.Optimization.LinearProgramming.Compression.ProxyRangeBits
import OAI.Optimization.LinearProgramming.Compression.ProxyBoundedRun

/-! Size bounds for the actual scan and unwind instructions in Section 3.4. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer
open RangeKernel

def rangeHeadBits (B fuel : ℕ) : ℕ := 10^9*(B+4) + 8*(B+fuel+8)

def rangeRegisterBound (B fuel : ℕ) : ℕ := 10^9 * rangeHeadBits B fuel

private theorem range_const_bits (d : ℕ) (r : ℚ) (h : Instr.const d r ∈ logRangeProgram) :
    ratBits r ≤ 4 := by
  let good : Instr → Bool
    | .const _ q => decide (ratBits q ≤ 4)
    | _ => true
  have hc : logRangeProgram.all good = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hc (.const d r) h)

theorem range_short_bound {s t : State ℚ} {n B fuel : ℕ} (hn : n ≤ 9)
    (hs : scalarBound (rangeHeadBits B fuel) s) (ht : runExactly logRangeProgram s n = some t) :
    RegisterBoundedRun logRangeProgram s n t (rangeRegisterBound B fuel) := by
  have hH : 4 ≤ rangeHeadBits B fuel := by dsimp [rangeHeadBits]; omega
  have h := RegisterBoundedRun.short hH (fun d r hr => (range_const_bits d r hr).trans hH) hs ht
  exact h.weaken (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hn))

theorem range_init_bound {s t : State ℚ} {n B fuel : ℕ} (hn : n ≤ 9) (hs : scalarBound B s)
    (ht : runExactly logRangeProgram s n = some t) :
    RegisterBoundedRun logRangeProgram s n t (rangeRegisterBound B fuel) ∧
      scalarBound (rangeHeadBits B fuel) t := by
  have hb : scalarBound (B+4) s := fun j => (hs j).trans (by omega)
  have h := RegisterBoundedRun.short (by omega : 4 ≤ B+4)
    (fun d r hr => (range_const_bits d r hr).trans (by omega)) hb ht
  have hn' : 10^n ≤ 10^9 := Nat.pow_le_pow_right (by decide) hn
  have hle : 10^n*(B+4) ≤ rangeHeadBits B fuel :=
    (Nat.mul_le_mul_right _ hn').trans (by dsimp [rangeHeadBits]; omega)
  have hle' : rangeHeadBits B fuel ≤ rangeRegisterBound B fuel := by
    dsimp [rangeRegisterBound]; omega
  exact ⟨h.weaken (hle.trans hle'), (h.weaken hle).finalBound⟩

theorem range_push_bound {s t : State ℚ} {z p : ℚ} {ptr n B fuel : ℕ}
    (hp : 8 ≤ ptr) (hh : Scan s z p (n+1) ptr) (hpz : p ≤ z)
    (hb : scalarBound (rangeHeadBits B fuel) s) (hnew : ratBits (p*p) ≤ rangeHeadBits B fuel)
    (hr : runExactly logRangeProgram s 7 = some t) : scalarBound (rangeHeadBits B fuel) t := by
  obtain ⟨pc, go, h₀, h₁, h₂, h₃, h₄, hn, hz, h8, hptr⟩ := hh
  have ha : ptr ≠ 2 := by omega
  have ha' : 2 ≠ ptr := by omega
  have hpb : ratBits p ≤ rangeHeadBits B fuel := h₂ ▸ hb 2
  simp [runExactly, step, logRangeProgram, execInstr, State.putData, State.putIndex,
    Function.update, pc, go, h₀, h₂, hn, hz, hptr, hpz.not_gt, ha'] at hr
  rw [← hr]
  repeat' apply update_bound
  all_goals first | exact hb | exact hpb | exact hnew

theorem range_base_bound {s t : State ℚ} {z p : ℚ} {ptr n H : ℕ}
    (hh : Scan s z p n ptr) (hz : z < p) (hb : scalarBound H s)
    (hr : runExactly logRangeProgram s 1 = some t) : scalarBound H t := by
  obtain ⟨pc, go, h₀, _, h₂, _⟩ := hh
  simp [runExactly, step, logRangeProgram, execInstr, pc, go, h₀, h₂, hz] at hr
  rw [← hr]; exact hb

theorem range_saturate_bound {s t : State ℚ} {z p : ℚ} {ptr H : ℕ}
    (hh : Scan s z p 0 ptr) (hz : p ≤ z) (hb : scalarBound H s)
    (hr : runExactly logRangeProgram s 3 = some t) : scalarBound H t := by
  obtain ⟨pc, go, h₀, _, h₂, _, _, hzero, hix, _⟩ := hh
  simp [runExactly, step, logRangeProgram, execInstr, pc, go, h₀, h₂, hzero, hix, hz.not_gt] at hr
  rw [← hr]; exact hb

/-- Returning one binary digit stores the trial product and the explicit doubled
exponent. Each stored value therefore has its independent, input-sensitive bound. -/
theorem range_unwind_bound {s t : State ℚ} {z p q : ℚ} {ptr e H : ℕ}
    (hptr : 8 ≤ ptr) (hh : Unwind s z (ptr+1) e q) (hsav : s.data ptr = p)
    (hb : scalarBound H s) (hprod : ratBits (q*p) ≤ H)
    (heven : ratBits (2*(e:ℚ)) ≤ H) (hodd : ratBits (2*(e:ℚ)+1) ≤ H)
    (hr : runExactly logRangeProgram s (if z < q*p then 6 else 9) = some t) :
    scalarBound H t := by
  obtain ⟨pc, go, h₀, h₁, h₃, h₄, h8, hp⟩ := hh
  have hl : 8 < ptr+1 := by omega
  have hs : ratBits p ≤ H := hsav ▸ hb ptr
  have he : (e:ℚ)+e = 2*e := by ring
  by_cases h : z < q*p <;>
    simp (config := {maxSteps := 50000}) [runExactly, step, logRangeProgram, execInstr,
      State.putData, State.putIndex, Function.update, pc, go, h₀, h₁, h₃, h₄, h8, hp,
      hsav, hl, h, he] at hr
  all_goals
    rw [← hr]
    repeat' apply update_bound
    all_goals first | exact hb | exact hs | exact hprod | exact heven | exact hodd

end Compression
end LinearProgramming
end Optimization
end OAI
