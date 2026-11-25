import OAI.Computability.BorderVNP.CellFragmentWords
import OAI.Computability.BorderVNP.CellFieldDecoder

/-! # Decoding the loop trip count on private tapes

The number of copies comes in binary. Reversing its little-endian digits onto a framed
stack permits the existing doubling parser to prepare the unary iteration counter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open VPVNP.RAMTape RationalHitting.StackLanguage

private def prepBody (b : Bool) : Routine (Fin 2) (Unit ⊕ Unit) :=
  (Routine.push 1 b).followedBy (Routine.push 1 true)

private def prepLoop :=
  Routine.popLoop 0 (fun _ => true) (prepBody false) (prepBody true)

private def prep : FiniteRoutine (Fin 2) :=
  .ofRoutine ((Routine.push 1 false).followedBy prepLoop)

private def two (x y : List Bool) : Stacks (Fin 2) := ![x,y]

private theorem two_right (x y : List Bool) : two x y 1 = y := rfl

private theorem setFirst (x y z : List Bool) : Function.update (two x y) 0 z = two z y := by
  funext i; fin_cases i <;> simp [two]

private theorem setSecond (x y z : List Bool) : Function.update (two x y) 1 z = two x z := by
  funext i; fin_cases i <;> simp [two]

private theorem prepBody_run (b : Bool) (x y : List Bool) :
    (prepBody b).Runs 2 (two x y) (two x (true :: b :: y)) := by
  apply Routine.Runs.followedBy (u := two x (b :: y)) (n := 1) (m := 1)
  · simpa only [setSecond,two_right] using Routine.runs_push 1 b (two x y)
  · simpa only [setSecond,two_right] using Routine.runs_push 1 true (two x (b :: y))

private def tags : List Bool → List Bool
  | [] => []
  | b :: xs => true :: b :: tags xs

private theorem tags_append (x y : List Bool) : tags (x++y) = tags x ++ tags y := by
  induction x with | nil => rfl | cons b x ih => simp [tags, ih]

private theorem frame_eq (x : List Bool) : FieldDecoder.frame x = tags x ++ [false] := by
  induction x with | nil => rfl | cons b x ih => simp [FieldDecoder.frame, tags, ih]

private theorem prepLoop_run (x y : List Bool) :
    prepLoop.Runs (3*x.length+1) (two x y) (two [] (tags x.reverse ++ y)) := by
  induction x generalizing y with
  | nil => exact Routine.Runs.popLoop_empty _ _ _ _ (show two [] y 0 = [] from rfl)
  | cons b x ih =>
    rw [List.length_cons, Nat.mul_succ, show 3*x.length+3+1 = 1+2+(3*x.length+1) by omega,
      List.reverse_cons, tags_append, List.append_assoc]
    have body := prepBody_run b x y
    have pop : Function.update (two (b::x) y) 0 x = two x y := setFirst ..
    cases b
    · exact Routine.Runs.popLoop_false_continue (s := two (false::x) y) 0 _ _ _ rfl rfl
        (pop ▸ body) (ih _)
    · exact Routine.Runs.popLoop_true_continue (s := two (true::x) y) 0 _ _ _ rfl rfl
        (pop ▸ body) (ih _)

private theorem prep_run (xs : List Bool) : prep.Runs (1+(3*xs.length+1)) (two xs [])
    (two [] (FieldDecoder.frame xs.reverse)) := by
  rw [frame_eq]
  apply Routine.Runs.followedBy (u := two xs [false])
  · simpa only [setSecond,two_right] using Routine.runs_push 1 false (two xs [])
  · exact prepLoop_run xs [false]

private theorem magnitude_append (xs ys : List Bool) (a : ℕ) :
    FieldDecoder.magnitude a (xs++ys) = FieldDecoder.magnitude (FieldDecoder.magnitude a xs) ys := by
  induction xs generalizing a with | nil => rfl | cons b xs ih => exact ih (2*a+b.toNat)

private theorem magnitude_reverse (xs : List Bool) :
    FieldDecoder.magnitude 0 xs.reverse = wordValue xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [List.reverse_cons, magnitude_append, ih]
    cases b <;> simp [FieldDecoder.magnitude, wordValue, Nat.add_comm]

variable {K : Type} [DecidableEq K]

private def ports (src : K) : Fin 2 → K ⊕ Bool := ![.inl src,.inr false]
private def fieldPorts (dst : K) : FieldDecoder.Port → K ⊕ Bool
  | .input => .inr false
  | .count => .inl dst
  | .scratch => .inr true

private def finished (q : FieldDecoder.Phase) := q == .done

/-- Binary source is consumed, destination receives one marker per iteration. -/
def loopBound (src dst : K) : Fragment K where
  Scratch := Bool
  body := (prep.onPorts (ports src)).followedBy
    (.ofStackCode FieldDecoder.code (fieldPorts dst) .tag finished)

private def middle (s : Stacks K) (src : K) (xs : List Bool) : Stacks (K ⊕ Bool) :=
  Sum.elim (Function.update s src []) (fun b => if b then [] else FieldDecoder.frame xs.reverse)

/-- The true number of loop iterations is decoded privately at cost proportional to the
digit length times the local trip count, including a zero bound. -/
theorem loopBound_run {src dst : K} (hd : src ≠ dst) (s : Stacks K) (a : ℕ)
    (hs : s src = a.bits) (ht : s dst = []) :
    ∃ d ≤ (7*a+8)*a.bits.length+3, (loopBound src dst).Runs d s
      (Function.update (Function.update s src []) dst (List.replicate a true)) := by
  let xs := a.bits
  have hm : FieldDecoder.magnitude 0 xs.reverse = a := (magnitude_reverse xs).trans (wordValue_bits a)
  have clock := FieldDecoder.steps_le 0 xs.reverse
  rw [hm, List.length_reverse] at clock
  refine ⟨(1+(3*xs.length+1))+FieldDecoder.steps 0 xs.reverse, ?_, ?_⟩
  · dsimp only [xs] at *
    rw [show 7*a+8 = 3+(7*a+5) by omega, Nat.add_mul]; omega
  apply FiniteRoutine.Runs.followedBy (t := middle s src xs)
  · have hp : Function.Injective (ports src) := by
      intro i j h; fin_cases i <;> fin_cases j <;> simp_all [ports]
    apply prep.runs_onPorts_framed hp (prep_run xs)
    · intro i; fin_cases i
      · exact hs
      · rfl
    · intro i; fin_cases i
      · exact Function.update_self ..
      · rfl
    · intro j hj
      rcases j with (k | b)
      · have hn : k ≠ src := fun he => hj 0 (congrArg Sum.inl he.symm)
        exact Function.update_of_ne hn ..
      · cases b with | true => rfl | false => exact (hj 1 rfl).elim
  · have r := FieldDecoder.run xs.reverse [] 0
    rw [List.append_nil, hm] at r
    have hp : Function.Injective (fieldPorts dst) := by
      intro i j h; cases i <;> cases j <;> simp_all [fieldPorts]
    have hn : ∀ q, finished q = true → (FieldDecoder.code q).returns = true := by
      intro q h; cases q <;> simp_all [finished, FieldDecoder.code, StackOp.returns]
    apply FiniteRoutine.runs_ofStackCode_framed (ports := fieldPorts dst) (normal := finished)
      hp rfl rfl hn r
    · intro i; cases i with
      | input | scratch => rfl
      | count => exact (Function.update_of_ne hd.symm ..).trans ht
    · intro i; cases i with
      | input | scratch => rfl
      | count => exact Function.update_self ..
    · intro j hj
      rcases j with (k|b)
      · have hn : k ≠ dst := fun he => hj .count (congrArg Sum.inl he.symm)
        exact Function.update_of_ne hn ..
      · cases b
        · exact (hj .input rfl).elim
        · exact (hj .scratch rfl).elim

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
