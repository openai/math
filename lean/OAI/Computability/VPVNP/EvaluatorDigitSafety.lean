import OAI.Computability.VPVNP.StructuredStackSafe
import OAI.Computability.VPVNP.EvaluatorDigitCallbacks
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Clock and storage along every branch of a digit countdown

A decremented digit can cause many nondeterministic matrix queries. Across
these queries the two counter stacks hold at most the original width, even
on a path that eventually rejects. The callback must itself supply a clock
and storage guarantee for every branch, and preserve the counters whenever
it returns normally.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitSafety

open RAMTape TapeWord EvaluatorDigitRepeat EvaluatorDigitCallbacks

variable {K Q S : Type*} [DecidableEq K]
variable (src tmp : K) (hne : src ≠ tmp) (body : Routine K Q)
variable (safe : Stacks K → Prop) (cont : ℕ → Stacks K → Prop)
variable (base : Stacks K) (w : ℕ)

include hne in
private theorem read_src (xs ys : List Bool) : frame src tmp base xs ys src = xs := by
  simp [frame, hne]

include hne in
private theorem set_src (xs ys zs : List Bool) :
    Function.update (frame src tmp base xs ys) src zs = frame src tmp base zs ys := by
  simp [frame, Function.update_comm hne.symm]

private theorem set_tmp (xs ys zs : List Bool) :
    Function.update (frame src tmp base xs ys) tmp zs = frame src tmp base xs zs := by simp [frame]

private theorem read_tmp (xs ys : List Bool) : frame src tmp base xs ys tmp = ys := by simp [frame]

variable (hold : ∀ xs ys : List Bool, xs.length + ys.length ≤ w → safe (frame src tmp base xs ys))

local notation "ok" => Routine.SafeFrom (repeatRoutine src tmp body) safe cont
local notation "st" => frame src tmp base

include hne hold in
private theorem scanFalse (n : ℕ) (xs ys : List Bool) (h : xs.length+ys.length+1 ≤ w) :
    ok (n+2) (some .scan) (st (false :: xs) ys) ↔ ok n (some .scan) (st xs (true :: ys)) := by
  have ha := hold (false :: xs) ys (by simp; omega)
  have hb := hold xs ys (by omega)
  simp [Routine.SafeFrom, repeatRoutine, read_src src tmp hne, read_tmp, set_src src tmp hne, set_tmp, ha, hb]

include hne hold in
private theorem scanTrue (n : ℕ) (xs ys : List Bool) (h : xs.length+ys.length+1 ≤ w) :
    ok (n+2) (some .scan) (st (true :: xs) ys) ↔ ok n (some .restore) (st (false :: xs) ys) := by
  have ha := hold (true :: xs) ys (by simp; omega)
  have hb := hold xs ys (by omega)
  simp [Routine.SafeFrom, repeatRoutine, read_src src tmp hne, set_src src tmp hne, ha, hb]

include hne hold in
private theorem scanNil (n : ℕ) (ys : List Bool) (h : ys.length ≤ w) :
    ok (n+1) (some .scan) (st [] ys) ↔ ok n (some .discard) (st [] ys) := by
  have ha := hold [] ys (by simpa using h)
  simp [Routine.SafeFrom, repeatRoutine, read_src src tmp hne, set_src src tmp hne, ha]

include hne hold in
private theorem restoreBit (n : ℕ) (xs ys : List Bool) (h : xs.length+ys.length+1 ≤ w) :
    ok (n+2) (some .restore) (st xs (true :: ys)) ↔ ok n (some .restore) (st (true :: xs) ys) := by
  have ha := hold xs (true :: ys) (by simp; omega)
  have hb := hold xs ys (by omega)
  simp [Routine.SafeFrom, repeatRoutine, read_tmp, set_tmp, read_src src tmp hne, set_src src tmp hne, ha, hb]

include hne hold in
private theorem scanZeros (l n : ℕ) (xs ys : List Bool) (h : l+xs.length+ys.length ≤ w) :
    ok (n+2*l) (some .scan) (st (List.replicate l false ++ xs) ys) ↔
      ok n (some .scan) (st xs (List.replicate l true ++ ys)) := by
  induction l generalizing ys with
  | zero => simp
  | succ l ih =>
    rw [show n+2*(l+1) = n+2*l+2 by omega, List.replicate_succ, List.cons_append,
      scanFalse src tmp hne body safe cont base w hold _ _ _ (by simp; omega),
      ih (true::ys) (by simp; omega), List.replicate_succ', List.append_assoc]
    rfl

include hne hold in
private theorem restoreOnes (l n : ℕ) (xs : List Bool) (h : xs.length+l ≤ w) :
    ok (n+2*l+1) (some .restore) (st xs (List.replicate l true)) ↔
      ok n (some (.call body.entry)) (st (List.replicate l true ++ xs) []) := by
  induction l generalizing xs with
  | zero =>
    have ha := hold xs [] (by simpa using h)
    simp [Routine.SafeFrom, repeatRoutine, read_tmp, set_tmp, ha]
  | succ l ih =>
    rw [show n+2*(l+1)+1 = n+2*l+1+2 by omega]
    nth_rw 1 [List.replicate_succ]
    rw [restoreBit src tmp hne body safe cont base w hold _ _ _ (by simp; omega),
      ih (true::xs) (by simp; omega), List.replicate_succ', List.append_assoc]
    rfl

include hold in
private theorem discardOnes (l n : ℕ) (h : l ≤ w) :
    ok (n+l+1) (some .discard) (st [] (List.replicate l true)) ↔ cont n (st [] []) := by
  induction l with
  | zero =>
    have ha := hold [] [] (by simp)
    simp [Routine.SafeFrom, repeatRoutine, read_tmp, set_tmp, ha]
  | succ l ih =>
    have ha := hold [] (true::List.replicate l true) (by simpa using h)
    rw [show n+(l+1)+1 = n+l+1+1 by omega, List.replicate_succ]
    simpa only [Routine.SafeFrom, repeatRoutine, read_tmp, List.head?_cons, List.tail_cons, Option.isSome_some,
      ↓reduceIte, set_tmp, ha, true_and] using ih (by omega)

include hne hold in
private theorem safeZero (fuel : ℕ) :
    (repeatRoutine src tmp body).Safe safe cont (fuel+(3*w+2)) (st (List.replicate w false) []) ↔
      cont fuel (st [] []) := by
  change ok _ (some .scan) _ ↔ _
  rw [show fuel+(3*w+2) = (fuel+w+1+1)+2*w by omega]
  have h := scanZeros src tmp hne body safe cont base w hold w (fuel+w+1+1) [] [] (by simp)
  simp only [List.append_nil] at h
  rw [h, scanNil src tmp hne body safe cont base w hold _ _ (by simp)]
  exact discardOnes src tmp body safe cont base w hold w fuel le_rfl

include hne hold in
private theorem safePositive (l fuel : ℕ) (xs : List Bool) (hw : l+1+xs.length ≤ w) :
    (repeatRoutine src tmp body).Safe safe cont (fuel+(4*l+3)) (st (List.replicate l false ++ true::xs) []) ↔
      body.Safe safe ((repeatRoutine src tmp body).Safe safe cont) fuel
        (st (List.replicate l true ++ false::xs) []) := by
  change ok _ (some .scan) _ ↔ _
  rw [show fuel+(4*l+3) = (fuel+2*l+1+1+1)+2*l by omega,
    scanZeros src tmp hne body safe cont base w hold _ _ _ _ (by simp; omega), List.append_nil,
    scanTrue src tmp hne body safe cont base w hold _ _ _ (by simp; omega),
    restoreOnes src tmp hne body safe cont base w hold _ _ _ (by simp; omega)]
  exact Routine.safeFrom_install (repeatRoutine src tmp body) body State.call (some .scan)
    (fun _ => rfl) safe cont fuel (some body.entry) _

include hne in
/-- A safety condition checked at every callback instruction and at every
countdown instruction holds throughout the full repetition. All normal
returns present empty counter stacks and reserve at least `extra` more
instructions. Abnormally terminating branches satisfy the same time and
storage checks up to their halt. -/
theorem repeat_safe (bank : S → Stacks K) (w B : ℕ)
    (frames : ∀ x (xs ys : List Bool), xs.length+ys.length ≤ w → safe (frame src tmp (bank x) xs ys))
    (callback : ∀ (x : S) (bits : List Bool), bits.length = w →
      ∀ (extra fuel : ℕ), extra+B ≤ fuel → ∀ c,
        (∀ y n, extra ≤ n → c n (frame src tmp (bank y) bits [])) →
          body.Safe safe c fuel (frame src tmp (bank x) bits []))
    (d : ℕ) (bits : List Bool) (hw : bits.length = w) (hd : value bits = d)
    (x : S) (extra fuel : ℕ) (hf : extra+repeatBudget w B d ≤ fuel)
    (finish : ∀ y n, extra ≤ n → cont n (frame src tmp (bank y) [] [])) :
    (repeatRoutine src tmp body).Safe safe cont fuel (frame src tmp (bank x) bits []) := by
  induction d generalizing bits x fuel with
  | zero =>
    have hz : bits = List.replicate w false := eq_of_length_value (by simpa using hw) (by simpa using hd)
    subst bits
    have h₀ : 3*w+2 ≤ repeatBudget w B 0 := by simp [repeatBudget]; omega
    rw [← Nat.sub_add_cancel (show 3*w+2 ≤ fuel by omega),
      safeZero src tmp hne body safe cont (bank x) w (frames x)]
    exact finish _ _ (by omega)
  | succ d ih =>
    obtain ⟨l, tail, rfl⟩ := EvaluatorDigitCallbacks.split_positive bits (by omega)
    let smaller := List.replicate l true ++ false :: tail
    have hs : smaller.length = w := by simpa [smaller] using hw
    have hv : value smaller = d := by have := value_decrement l tail; dsimp [smaller]; omega
    have hw' : l+1+tail.length ≤ w := by simp at hw; omega
    have hb : repeatBudget w B (d+1) = repeatBudget w B d + (4*w+B+3) := Nat.succ_mul ..
    rw [hb] at hf
    have enough : extra+repeatBudget w B d+B ≤ fuel-(4*l+3) := by omega
    rw [← Nat.sub_add_cancel (show 4*l+3 ≤ fuel by omega), safePositive src tmp hne body safe cont (bank x)
      w (frames x) _ _ _ hw']
    apply callback x smaller hs (extra+repeatBudget w B d) _ enough
    intro y n hn
    exact ih smaller hs hv y n hn

section Storage

variable [Fintype K]

private theorem update_length (s : Stacks K) (p : K) (bs : List Bool) :
    ∑ k, (Function.update s p bs k).length ≤ (∑ k, (s k).length) + bs.length := by
  calc
    _ ≤ ∑ k, ((s k).length + if k = p then bs.length else 0) := Finset.sum_le_sum (fun k _ => by
      by_cases hp : k = p <;> simp [hp])
    _ = _ := by simp [Finset.sum_add_distrib]

/-- The countdown's local storage allowance is the width of one digit. -/
theorem frame_length_le (base : Stacks K) (src tmp : K) (xs ys : List Bool) :
    ∑ k, (frame src tmp base xs ys k).length ≤ (∑ k, (base k).length) + xs.length + ys.length :=
  (update_length _ _ _).trans (Nat.add_le_add_right (update_length _ _ _) _)

include hne in
/-- On the closed binary-choice machine, all branches halt within the clock
and every reachable configuration fits the peak bound. The final instruction
closes a normal return with the selected halt outcome. -/
theorem repeat_space_clock (bank : S → Stacks K) (w B A callbackSpace : ℕ)
    (base_bound : ∀ x, ∑ k, (bank x k).length ≤ A)
    (callback : ∀ (x : S) (bits : List Bool), bits.length = w →
      ∀ (extra fuel : ℕ), extra+B ≤ fuel → ∀ c,
        (∀ y n, extra ≤ n → c n (frame src tmp (bank y) bits [])) →
          body.Safe (fun s => ∑ k, (s k).length ≤ max (A+w) callbackSpace)
            c fuel (frame src tmp (bank x) bits []))
    (bits : List Bool) (hw : bits.length = w) (x : S) (outcome : Bool) :
    let r := repeatRoutine src tmp body
    let input := frame src tmp (bank x) bits []
    StopsWithin (r.close outcome) (1+repeatBudget w B (value bits)) (some r.entry) input ∧
      ∀ ⦃q s⦄, StackCompiler.Reach (r.close outcome) (some r.entry) input q s →
        ∑ k, (s k).length ≤ max (A+w) callbackSpace := by
  let limit (s : Stacks K) := ∑ k, (s k).length ≤ max (A+w) callbackSpace
  have fits (y : S) (xs ys : List Bool) (hh : xs.length+ys.length ≤ w) :
      limit (frame src tmp (bank y) xs ys) := by
    have h := frame_length_le (bank y) src tmp xs ys
    have h' := base_bound y
    dsimp [limit]
    exact (show ∑ k, (frame src tmp (bank y) xs ys k).length ≤ A+w by omega).trans (le_max_left ..)
  have h := repeat_safe src tmp hne body limit (fun n s => 0<n ∧ limit s) bank w B fits
    callback (value bits) bits hw rfl x 1 (1+repeatBudget w B (value bits)) le_rfl
    (fun y n hn => ⟨hn, fits y [] [] (by simp)⟩)
  exact ⟨h.stopsWithin outcome (fun _ _ hc => hc.1),
    fun _ _ path => h.reach outcome (fun _ _ hc => hc.2) path⟩

end Storage

end EvaluatorDigitSafety

end VPVNP
end Computability
end OAI
