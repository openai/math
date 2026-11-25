import OAI.Optimization.LinearProgramming.RAM.Basic
import OAI.Optimization.LinearProgramming.FieldTransfer.Execution
import OAI.Optimization.LinearProgramming.PrimalDual.Bits

/-! Bounds for fixed-length scalar RAM instruction segments over the rationals. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer
open OAI.Optimization.LinearProgramming.PrimalDual (ratBits_mul_le ratBits_sub_le ratBits_inv_le ratBits_neg)

abbrev RegBound (B : ℕ) (f : ℕ → ℚ) : Prop := ∀ j, ratBits (f j) ≤ B

theorem update_bound {f : ℕ → ℚ} {B : ℕ} (hf : RegBound B f)
    (j : ℕ) {q : ℚ} (hq : ratBits q ≤ B) : RegBound B (Function.update f j q) := by
  intro l
  by_cases h : l = j <;> simp [Function.update, h, hq, hf]

private theorem put_bound {s : State ℚ} {B : ℕ} (hs : scalarBound B s)
    (j : ℕ) {q : ℚ} (hq : ratBits q ≤ B) : scalarBound B (s.putData j q) :=
  update_bound hs j hq

theorem natCast_ratBits_le {n e : ℕ} (h : n ≤ 2 ^ e) : ratBits (n : ℚ) ≤ e + 3 := by
  have hn : n.log2 ≤ e := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · apply Nat.le_of_lt_succ
      apply (Nat.log2_lt hn).2
      rw [pow_succ]
      have := Nat.two_pow_pos e
      omega
  simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
  change 3+n.log2+0 ≤ e+3
  omega

/-- For a straight-line region of fixed length, one legal instruction increases
the previous register bound by at most a factor ten, as long as the program's
rational constants also fit. -/
theorem scalarStep_bound {p : Program} {H : ℕ} (hH : 4 ≤ H)
    (hconst : ∀ d q, Instr.const d q ∈ p → ratBits q ≤ H) {s t : State ℚ}
    (hs : scalarBound H s) (he : step p s = some t) : scalarBound (10*H) t := by
  have unchanged : scalarBound (10*H) s := fun j => (hs j).trans (by omega)
  have add (a b : ℕ) : ratBits (s.data a + s.data b) ≤ 10 * H := by
    have h := ratBits_sub_le (s.data a) (-s.data b)
    rw [sub_neg_eq_add, ratBits_neg] at h
    have ha := hs a; have hb := hs b; omega
  have sub (a b : ℕ) : ratBits (s.data a - s.data b) ≤ 10 * H := by
    have h := ratBits_sub_le (s.data a) (s.data b)
    have ha := hs a; have hb := hs b; omega
  have mul (a b : ℕ) : ratBits (s.data a * s.data b) ≤ 10 * H := by
    have h := ratBits_mul_le (s.data a) (s.data b)
    have ha := hs a; have hb := hs b; omega
  have div (a b : ℕ) : ratBits (s.data a / s.data b) ≤ 10 * H := by
    rw [div_eq_mul_inv]
    have h := ratBits_mul_le (s.data a) (s.data b)⁻¹
    have ha := hs a; have hb := hs b; have hinv := ratBits_inv_le (s.data b); omega
  unfold step at he
  cases hgo : s.output <;> rw [hgo] at he
  · cases hh : p[s.pc]? with
    | none => simp [hh] at he
    | some op =>
      rw [hh] at he
      have his := List.mem_of_getElem? hh
      cases op <;> simp only [execInstr] at he <;> (try split at he) <;>
        simp_all only [Option.some.injEq, reduceCtorEq]
      all_goals rw [← he]
      all_goals first
        | exact unchanged
        | apply put_bound unchanged
          first
            | exact unchanged _
            | exact add _ _
            | exact sub _ _
            | exact mul _ _
            | exact div _ _
            | simpa only [Rat.cast_id] using (hconst _ _ his).trans (show H ≤ 10*H by omega)
  · simp at he

/-- A coarse bound for a fixed number of instructions. Longer algorithms use
their mathematical invariant to reset the bound after each fixed-length block. -/
theorem scalarSteps_bound {p : Program} {s t : State ℚ} {H n : ℕ} (hH : 4 ≤ H)
    (hconst : ∀ d q, Instr.const d q ∈ p → ratBits q ≤ H)
    (hs : scalarBound H s) (ht : runExactly p s n = some t) :
    scalarBound (10 ^ n * H) t := by
  induction n generalizing t with
  | zero =>
    change some s = some t at ht
    cases Option.some.inj ht
    simpa using hs
  | succ n ih =>
    change (runExactly p s n).bind (step p) = some t at ht
    cases hv : runExactly p s n with
    | none => simp [hv] at ht
    | some v =>
      have hp : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by decide)
      have hmin : H ≤ 10 ^ n * H := by nlinarith
      have hstep := scalarStep_bound (hH.trans hmin) (fun d q hd => (hconst d q hd).trans hmin)
        (ih hv) (by simpa [hv] using ht)
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hstep

end Compression
end LinearProgramming
end Optimization
end OAI
