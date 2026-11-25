import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingBounds

/-! A uniformly polynomial physical bit-stack program for summing a variable-length
list of arbitrary reduced rationals. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open Procedure

/-- Shared bit width of the numerator magnitude and denominator. -/
private def fractionWidth (q : ℚ) : ℕ := max q.num.natAbs.size q.den.size

private theorem width_input (q : ℚ) : fractionWidth q ≤ (ratCode q).length := by
  rw [Wire.rat_length, fractionWidth]
  omega

private theorem width_output (q : ℚ) : (ratCode q).length ≤ 7 + 3 * fractionWidth q := by
  rw [Wire.rat_length, fractionWidth]
  omega

private theorem components_lt (q : ℚ) :
    q.num.natAbs < 2^(fractionWidth q) ∧ q.den < 2^(fractionWidth q) :=
  ⟨Nat.size_le.mp (le_max_left _ _), Nat.size_le.mp (le_max_right _ _)⟩

/-- Reduction to lowest terms cannot enlarge either part of the sum of two fractions. -/
private theorem add_width (q r : ℚ) :
    fractionWidth (q+r) ≤ fractionWidth q + fractionWidth r + 1 := by
  have hnum : (q+r).num.natAbs ≤ q.num.natAbs*r.den + r.num.natAbs*q.den := by
    rw [Rat.num_add]
    refine (Int.natAbs_ediv_le_natAbs _ _).trans ?_
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      Int.natAbs_add_le (q.num * (r.den : ℤ)) (r.num * (q.den : ℤ))
  have hd : (q+r).den ≤ q.den*r.den := by
    rw [Rat.den_add]
    exact Nat.div_le_self _ _
  have h1 := Nat.mul_lt_mul_of_lt_of_lt (components_lt q).1 (components_lt r).2
  have h2 := Nat.mul_lt_mul_of_lt_of_lt (components_lt r).1 (components_lt q).2
  have h3 := Nat.mul_lt_mul_of_lt_of_lt (components_lt q).2 (components_lt r).2
  rw [← pow_add] at h1 h2 h3
  rw [Nat.add_comm (fractionWidth r) (fractionWidth q)] at h2
  apply max_le
  · apply Nat.size_le.mpr
    rw [pow_succ]
    omega
  · apply Nat.size_le.mpr
    rw [pow_succ]
    omega

private theorem sum_fold_width (xs : List ℚ) (b : ℚ) :
    fractionWidth (xs.foldl (fun t x => x+t) b) ≤ fractionWidth b + (listCode ratCode xs).length := by
  induction xs generalizing b with
  | nil => simp [listCode]
  | cons x xs ih =>
    rw [List.foldl_cons, listCode_length_cons]
    have h := ih (x+b)
    have hx := width_input x
    have ha := add_width x b
    omega

private theorem sum_fold_value (xs : List ℚ) (b : ℚ) :
    xs.foldl (fun t x => x+t) b = xs.sum + b := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.sum_cons]; ring

/-- The clock applies to every input list and every intermediate folding prefix. -/
noncomputable def ratListSumP : Procedure (listCode ratCode) ratCode List.sum := by
  let p := foldList (0 : ℚ) ratAdd (Polynomial.C 3 * Polynomial.X + Polynomial.C 7) (by
    intro xs b i
    change (ratCode ((xs.take i).foldl (fun t x => x+t) b)).length ≤ _
    have ha := width_output ((xs.take i).foldl (fun t x => x+t) b)
    have hb := sum_fold_width (xs.take i) b
    have hc := listCode_length_take_le ratCode i xs
    have hd := width_input b
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega)
  exact (p.comp ((identity (listCode ratCode)).pair (constant (listCode ratCode) ratCode 0))).congrFun
    (by intro xs; simpa only [Function.comp_apply, id_eq, add_zero] using sum_fold_value xs 0)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
