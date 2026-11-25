import OAI.Computability.IntegerMultiplication.Code.Pace
import OAI.Computability.IntegerMultiplication.Code.Padding
import OAI.Computability.NearSquareRoot.CoprimeBox

/-! # Polynomial-time bounded search for coprime axes on the P192 stack compiler

The inner loop starts at the top of a candidate interval, drops one unary mark on
failure, and freezes at the first passing candidate. Its state never grows. Each
outer iteration prepends one of these bounded candidates to the list of axes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxScanTask

open IntegerMultiplication.Code
open CoprimeBox

abbrev TestInput := Tally × List Tally

def test (i : TestInput) : Bool := decide (i.1.length.Coprime (2 * (i.2.map List.length).prod))

abbrev Cursor := Tally × Bool

def step (i : List Tally × Cursor) : Cursor :=
  bif i.2.2 || test (i.2.1, i.1) then (i.2.1, true) else (i.2.1.tail, false)

private theorem step_poly (h : Poly test) : Poly step := by
  have ht : Easy (fun t : Tally => t.tail) := by
    have he : (fun t : Tally => t.tail) = (fun t => List.casesOn t [] (fun _ xs => xs)) := by
      funext t; cases t <;> rfl
    rw [he]
    exact Easy.listCase [] (Easy.snd (Y := Tally))
  have hor : Poly (fun p : Bool × Bool => p.1 || p.2) := (Easy.finite _).poly
  have hc : Poly (fun i : List Tally × Cursor => i.2.2 || test (i.2.1, i.1)) := by
    apply Poly.compose (f := fun i : List Tally × Cursor => (i.2.2, test (i.2.1,i.1))) _ hor
    apply Poly.pair (by fun_prop)
    exact Poly.compose (by fun_prop) h
  unfold step
  apply Poly.choose hc (by fun_prop)
  exact Poly.pair ((show Poly (fun i : List Tally × Cursor => i.2.1) by fun_prop).compose ht.poly) ((Easy.const false).poly)

private theorem step_size (a : List Tally) (c : Cursor) : size (step (a,c)) ≤ size c := by
  obtain ⟨u,b⟩ := c
  simp only [step]
  cases (b || test (u,a)) <;> simp [size_prod, size_tally, show size b = 1 from rfl, show size true = 1 from rfl, show size false = 1 from rfl]

private theorem step_frozen (a : List Tally) (u : Tally) (i : ℕ) :
    ((fun c => step (a,c))^[i]) (u,true) = (u,true) := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [Function.iterate_succ_apply, step] using ih

private theorem search_eq (a : List Tally) (lo h : ℕ) :
    (((fun c => step (a,c))^[h]) (tally (lo+h),false)).1 =
      tally (search lo (2 * (a.map List.length).prod) h) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [Function.iterate_succ_apply, search]
    by_cases hp : (lo + (h+1)).Coprime (2 * (a.map List.length).prod)
    · simp only [ite_eq_left hp]
      rw [show step (a, tally (lo + (h+1)), false) = (tally (lo + (h+1)), true) by
        simp [step, test, hp]]
      rw [step_frozen]
    · simp only [ite_eq_right hp]
      rw [show step (a, tally (lo + (h+1)), false) = (tally (lo + h), false) by
        simp only [step, test, tally_length, decide_eq_false hp, Bool.false_or, Bool.cond_false]
        simp [← Nat.add_assoc]]
      exact ih

/-- Static inputs are the unary lower endpoint and window width. -/
abbrev Interval := Tally × Tally

def chooseAxis (i : Interval × List Tally) : Tally :=
  tally (search i.1.1.length (2 * (i.2.map List.length).prod) i.1.2.length)

theorem chooseAxis_poly (h : Poly test) : Poly chooseAxis := by
  have ride := Poly.bounder step (step_poly h) 0 (by simpa using step_size)
  have init : Poly (fun i : Interval × List Tally => (i.1.2, i.2, i.1.1 ++ i.1.2, false)) := by fun_prop
  have pass := (init.compose ride).fstCompose
  convert pass using 1
  funext i
  have hi : i.1.1 ++ i.1.2 = tally (i.1.1.length + i.1.2.length) := by
    rw [← List.length_append, recover_tally]
  dsimp only [chooseAxis]
  rw [hi]
  exact (search_eq ..).symm

def addAxis (i : Interval × List Tally) : List Tally := chooseAxis i :: i.2

private theorem addAxis_size (w : Interval) (a : List Tally) :
    size (addAxis (w,a)) ≤ 2 * size w + size a := by
  have hm := (search_mem w.1.length (2*(a.map List.length).prod) w.2.length).2
  simp only [addAxis, chooseAxis, size_cons, size_prod, size_tally, tally_length]
  omega

/-- One unknown list of odd coprime moduli is computed by the same fixed program
for all `m`, endpoints, and window sizes. -/
def axesFrom (i : Tally × Interval) : List Tally :=
  ((fun a => addAxis (i.2,a))^[i.1.length]) []

theorem axesFrom_poly (h : Poly test) : Poly axesFrom := by
  have hAdd : Poly addAxis := (Poly.pair (chooseAxis_poly h) Easy.snd.poly).compose Poly.cons
  have iter := Poly.bounder addAxis hAdd 2 addAxis_size
  exact (show Poly (fun i : Tally × Interval => (i.1,i.2,([] : List Tally))) by fun_prop).compose iter

theorem axesFrom_fullAxes (k m : ℕ) :
    axesFrom (tally m, tally (BoxScale.span k - window k), tally (window k)) =
      (fullAxes k m).map tally := by
  simp only [axesFrom, tally_length]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [fullAxes, addAxis, chooseAxis, List.map_map, Function.comp_def]

end BoxScanTask

end NearSquareRoot
end Computability
end OAI
