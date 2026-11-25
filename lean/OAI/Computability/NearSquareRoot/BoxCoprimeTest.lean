import OAI.Computability.IntegerMultiplication.Code.Iter
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Testing a coprime box axis on the stack machine

Setup may write candidate axis lengths in unary: each is polynomial in the
address length. Subtractive Euclid then gives a polynomial-time test on a pair
of axes. Testing each previously chosen axis separately avoids expanding their
product in unary. The predicates `Easy` and `Poly` below quantify over actual
P192 stack programs that restore their scratch and parked data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxCoprimeTest

open IntegerMultiplication.Code

abbrev Pair := Tally × Tally

/-- One subtraction leaves a zero component fixed. -/
def step (p : Pair) : Pair :=
  bif Iter.small p then (p.1, (cutLists p).2) else ((cutLists (p.2, p.1)).2, p.2)

private theorem step_poly : Poly step := by
  have hlt := (Iter.small_easy (X := Unit) (Y := Unit)).poly
  have hcut := (easy_cut (X := Unit) (Z := Pair) Easy.identity).sndCompose.poly
  have hswap := (easy_cut (X := Unit) (Z := Pair) Easy.exchange).sndCompose.poly
  unfold step
  exact Poly.choose hlt (Easy.fst.poly.pair hcut) (hswap.pair Easy.snd.poly)

private theorem step_size (p : Pair) : size (step p) ≤ size p + 0 := by
  unfold step
  cases e : Iter.small p <;> simp [cutLists, size_prod, size_tally]

private theorem zero_left (y : Tally) : step ([], y) = ([], y) := by
  cases y <;> simp [step, Iter.small, cutLists]

private theorem zero_right (x : Tally) : step (x, []) = (x, []) := by
  simp [step, Iter.small, cutLists]

private theorem step_gcd (p : Pair) :
    ((step p).1.length).gcd (step p).2.length = p.1.length.gcd p.2.length := by
  by_cases h : p.1.length < p.2.length
  · simpa [step, Iter.small, h, cutLists] using Nat.gcd_sub_self_right h.le
  · simpa [step, Iter.small, h, cutLists] using Nat.gcd_sub_self_left (Nat.le_of_not_gt h)

private theorem iterate_sum (t : ℕ) (p : Pair) (ht : p.1.length + p.2.length ≤ t) :
    (step^[t] p).1.length + (step^[t] p).2.length = p.1.length.gcd p.2.length := by
  rcases p with ⟨x, y⟩
  by_cases hx : x = []
  · subst x
    rw [Function.iterate_fixed (zero_left y)]
    simp
  by_cases hy : y = []
  · subst y
    rw [Function.iterate_fixed (zero_right x)]
    simp
  have hx' : 0 < x.length := List.length_pos_iff.mpr hx
  have hy' : 0 < y.length := List.length_pos_iff.mpr hy
  cases t with
  | zero => simp only at ht; omega
  | succ t =>
    rw [Function.iterate_succ_apply, ← step_gcd (x, y)]
    apply iterate_sum
    by_cases h : x.length < y.length <;>
      simp [step, Iter.small, cutLists, h] at * <;> omega
termination_by t

/-- Euclid finishes in at most the sum of the unary argument lengths. -/
def gcd (p : Pair) : Tally :=
  let s := ride step (p.1 ++ p.2, p)
  s.1 ++ s.2

theorem gcd_poly : Poly gcd := by
  have hinit : Poly (fun p : Pair => (p.1 ++ p.2, p)) := by fun_prop
  have h := hinit.compose (Poly.rider step step_poly 0 step_size)
  exact Poly.app h.fstCompose h.sndCompose

@[simp] theorem gcd_length (x y : Tally) : (gcd (x,y)).length = x.length.gcd y.length := by
  unfold gcd
  simp only [List.length_append, ride_t]
  exact iterate_sum _ _ (by simp)

def coprime (p : Pair) : Bool := decide ((gcd p).length = 1)

theorem coprime_poly : Poly coprime := by
  have h := (gcd_poly.pair ((Easy.const (tally 1)).poly)).compose
    (Iter.linked (X := Unit) (Y := Unit)).poly
  change Poly (fun p : Pair => decide ((gcd p).length = 1))
  simpa only [tally_length] using h

@[simp] theorem coprime_eq (x y : Tally) :
    coprime (x,y) = decide (x.length.Coprime y.length) := by
  simp [coprime, Nat.Coprime]

/-- Test all old axes and the factor two of the residual axis. -/
def compatible (p : Tally × List Tally) : Bool :=
  (polyPush coprime (p.1, tally 2 :: p.2)).foldl (· && ·) true

theorem compatible_poly : Poly compatible := by
  have hinit : Poly (fun p : Tally × List Tally => (p.1,tally 2 :: p.2)) := by fun_prop
  have h := hinit.compose (Poly.push [] [] coprime_poly)
  have hf := Poly.fold_left (f := fun p : Bool × Bool => p.1 && p.2)
    (Easy.finite _).poly 1 1 (by intro s l hl; change 1 ≤ _; simp)
  exact (h.pair ((Easy.const true).poly)).compose hf

private theorem and_fold (l : List Bool) (s : Bool) :
    l.foldl (· && ·) s = true ↔ s = true ∧ ∀ v ∈ l, v = true := by
  induction l generalizing s with
  | nil => simp
  | cons v l ih => simp [List.foldl_cons, ih, and_assoc]

theorem compatible_iff (a : Tally) (xs : List Tally) :
    compatible (a,xs) = true ↔ a.length.Coprime 2 ∧ ∀ b ∈ xs, a.length.Coprime b.length := by
  simp [compatible, and_fold, polyPush]

/-- Compilable predicate for the test in the descending Jacobsthal search. -/
theorem test_poly :
    Poly (fun p : Tally × List Tally =>
      decide (p.1.length.Coprime (2 * (p.2.map List.length).prod))) := by
  suffices he : compatible = (fun p : Tally × List Tally =>
      decide (p.1.length.Coprime (2 * (p.2.map List.length).prod))) from he ▸ compatible_poly
  funext ⟨a, xs⟩
  apply Bool.eq_iff_iff.mpr
  simp [compatible_iff, Nat.coprime_mul_iff_right, Nat.coprime_list_prod_right_iff]

end BoxCoprimeTest

end NearSquareRoot
end Computability
end OAI
