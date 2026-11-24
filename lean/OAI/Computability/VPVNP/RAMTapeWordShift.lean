import OAI.Computability.VPVNP.RAMTapeWordShiftBorrow
import OAI.Computability.VPVNP.RAMTapeWordShiftMove
import OAI.Computability.VPVNP.RAMTapeWordShiftValue
import Mathlib.Tactic.Linarith

/-!
# Fixed-stack programs for variable word shifts

The decrement loop processes at most the width of the data word, including
when the shift amount represents an exponentially larger natural number.
Reversing the data before and after the loop implements a left shift. Both
variants leave a little-endian word and empty all their scratch stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Shift

open RAMTape BurstRAM

/-- The entry port depends on the operation, so a left shift can first reverse
its input onto the data stack. -/
def input (left : Bool) (amount data : List Bool) : Stacks Reg :=
  if left then store amount [] data [] [] else store amount data [] [] []

/-- Returned stack layout for a variable shift. Left shifts place the final word on the
temporary port, and right shifts place it on the output port. -/
def output (left : Bool) (bits : List Bool) : Stacks Reg :=
  if left then store [] [] bits [] [] else store [] [] [] bits []

local macro "shift_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_store])

/-- The data prefix is dropped one bit at a time. The padding is limited by
the number of bits actually removed. -/
private theorem loop_run (left : Bool) (a d o : List Bool) :
    ∃ k ≤ (d.length + 1) * (5 * (a.length + 1) + 12) + 4 * d.length + 3,
      StackRuns (code left) k .loop (store a d [] o []) .finish
        (store [] [] [] (d.drop (value a) ++ (List.replicate (min (value a) d.length) false ++ o)) []) := by
  induction d generalizing a o with
  | nil =>
    refine ⟨(a.length + 1) + 1, by simp; omega, ?_⟩
    shift_step
    simpa using discard_run left a [] [] o []
  | cons b d ih =>
    obtain ⟨kb, hkb, run⟩ := borrow_run left b a d [] o
    by_cases hz : value a = 0
    · simp only [hz, ↓reduceIte] at run
      have hr := reverseData_run left [] (b :: d) [] o []
      have ht := restoreData_run left [] [] (b :: d).reverse o []
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hr ht
      let m := 2 * (b :: d).length + 1
      have hcopy : StackRuns (code left) ((m + m) + 1) (.zero b) (store [] d [] o [])
          .finish (store [] [] [] ((b :: d) ++ o) []) := by
        shift_step
        exact hr.trans ht
      refine ⟨(kb + ((m + m) + 1)) + 1, ?_, ?_⟩
      · simp only [m, List.length_cons]
        rw [Nat.succ_mul (d.length + 1)]
        omega
      · simp only [hz, Nat.zero_min, List.replicate_zero, List.nil_append, List.drop_zero]
        shift_step
        exact run.trans hcopy
    · simp only [hz, ↓reduceIte] at run
      obtain ⟨a', hlen, hval, hrun⟩ := run
      obtain ⟨kt, hkt, htail⟩ := ih a' (false :: o)
      rw [hlen] at hkt
      have hc : StackRuns (code left) (kt + 1) .consume (store a' d [] o []) .finish
          (store [] [] [] (d.drop (value a') ++
            (List.replicate (min (value a') d.length) false ++ false :: o)) []) := by
        shift_step
        exact htail
      refine ⟨(kb + (kt + 1)) + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        rw [Nat.succ_mul (d.length + 1)]
        omega
      · have he : value a = value a' + 1 := by omega
        simp only [he, List.drop_succ_cons, List.length_cons, Nat.succ_min_succ,
          List.replicate_succ', List.append_assoc, List.singleton_append]
        shift_step
        exact hrun.trans hc

private theorem start_run (left : Bool) (a x : List Bool) :
    ∃ k ≤ 2 * x.length + 2, StackRuns (code left) k .start (input left a x) .loop
      (store a (if left then x.reverse else x) [] [] []) := by
  cases left with
  | false =>
    exact ⟨1, by omega, .cons (.goto rfl) (.nil ..)⟩
  | true =>
    refine ⟨(2 * x.length + 1) + 1, by omega, .cons (.goto rfl) ?_⟩
    simpa [input] using prepare_run true a [] x [] []

private theorem finish_run (left : Bool) (y : List Bool) :
    ∃ k ≤ 2 * y.length + 2, StackRuns (code left) k .finish (store [] [] [] y []) .done
      (output left (if left then y.reverse else y)) := by
  cases left with
  | false =>
    exact ⟨1, by omega, .cons (.goto rfl) (.nil ..)⟩
  | true =>
    refine ⟨(2 * y.length + 1) + 1, by omega, .cons (.goto rfl) ?_⟩
    simpa [output] using reverseOut_run true [] [] [] y []

/-- Both variable-shift opcodes have a width-independent control and five
stacks. The instruction bound is quadratic in the width, for every amount. -/
theorem shift_run {w : ℕ} (left : Bool) (x y : Word w) :
    ∃ k ≤ 40 * (w + 1) ^ 2, StackRuns (code left) k .start (input left (wordBits y) (wordBits x))
      .done (output left (wordBits ((if left then PrivateRAM.BinaryOp.shiftLeft else
        PrivateRAM.BinaryOp.shiftRight).eval x y))) := by
  let z := if left then (wordBits x).reverse else wordBits x
  let u := z.drop y.val ++ List.replicate (min y.val z.length) false
  have hz : z.length = w := by cases left <;> simp [z]
  have hu : u.length = w := by
    simp only [u, List.length_append, List.length_drop, List.length_replicate, hz]
    omega
  obtain ⟨ka, ha, hstart⟩ := start_run left (wordBits y) (wordBits x)
  obtain ⟨kb, hb, hcore⟩ := loop_run left (wordBits y) z []
  obtain ⟨kc, hc, hend⟩ := finish_run left u
  rw [length_wordBits] at ha
  rw [hz, length_wordBits] at hb
  rw [hu] at hc
  refine ⟨ka + kb + kc, by nlinarith, ?_⟩
  have core : StackRuns (code left) kb .loop (store (wordBits y) z [] [] []) .finish
      (store [] [] [] u []) := by simpa only [value_wordBits, List.append_nil, u] using hcore
  rw [← result_wordBits]
  simpa only [result, value_wordBits] using (hstart.trans core).trans hend

end TapeWord.Shift

end VPVNP
end Computability
end OAI
