import OAI.Computability.VPVNP.EvaluatorRadixDivision
import OAI.Computability.VPVNP.RAMTapeUnaryWordValue

/-! # Fixed-width address and tick increments for a team's burst probe -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstProbeStep

open VPVNP BurstRAM RAMTape

variable {K : Type} [DecidableEq K] {w : ℕ}

/-- The successor of a RAM word, including wraparound at the top address. -/
def next (a : Word w) : Word w := Fin.ofNat (2^w) (a.val+1)

private def scan : Routine Bool (Bool ⊕ (Bool × Bool)) where
  entry := .inl true
  code
    | .inl carry => .pop false fun b => b.map fun d => .inr (d ^^ carry, d && carry)
    | .inr (bit, carry) => .push true bit (some (.inl carry))

private def bank (word tmp : List Bool) : Stacks Bool
  | false => word
  | true => tmp

private theorem scan_runs (carry : Bool) (xs tmp : List Bool) :
    StackRuns scan.standalone (2*xs.length+1) (some (.inl carry)) (bank xs tmp) none
      (bank [] ((UnaryWord.incScan carry xs).1.reverse ++ tmp)) := by
  have update (a b v : List Bool) (i : Bool) : Function.update (bank a b) i v =
      (if i then bank a v else bank v b) := by funext j; cases i <;> cases j <;> rfl
  induction xs generalizing carry tmp with
  | nil =>
    refine .cons (.pop rfl) ?_
    simp only [bank, update, List.head?_nil, List.tail_nil, Option.map_none,
      Bool.false_eq_true, ↓reduceIte, UnaryWord.incScan, List.reverse_nil, List.nil_append]
    exact .nil ..
  | cons b xs ih =>
    rw [List.length_cons, Nat.mul_succ]
    refine .cons (.pop rfl) (.cons (.push rfl) ?_)
    simpa only [bank, update, Bool.false_eq_true, ↓reduceIte, List.tail_cons, List.head?_cons,
      Option.map_some, UnaryWord.incScan, List.reverse_cons, List.append_assoc, List.singleton_append]
      using ih (b && carry) ((b ^^ carry)::tmp)

private def small : FiniteRoutine Bool :=
  (FiniteRoutine.ofRoutine scan).followedBy (EvaluatorRadixDivision.reverseOnto true false)

private theorem small_runs (xs : List Bool) :
    small.Runs (4*xs.length+2) (bank xs []) (bank (UnaryWord.incScan true xs).1 []) := by
  let y := (UnaryWord.incScan true xs).1
  have first : (FiniteRoutine.ofRoutine scan).Runs (2*xs.length+1) (bank xs []) (bank [] y.reverse) := by
    change StackRuns scan.standalone _ (some (.inl true)) _ none _
    simpa only [List.append_nil] using scan_runs true xs []
  have last := EvaluatorRadixDivision.reverseOnto_runs (src := true) (dst := false) (by decide)
    (bank [] y.reverse) (bank y []) rfl (by simp [bank]) (fun k h h' => by cases k <;> contradiction)
  have hl : y.length = xs.length := UnaryWord.incScan_length ..
  simpa only [small, bank, List.length_reverse, hl,
    show 2*xs.length+1+(2*xs.length+1) = 4*xs.length+2 by omega] using first.followedBy last

private def counters (word tmp : K) : Bool → K
  | false => word
  | true => tmp

/-- Scan a word with one carry bit and reverse the result back onto its original stack. -/
def increment (word tmp : K) : FiniteRoutine K := small.onPorts (counters word tmp)

/-- The fixed-width increment uses four stack operations per bit, independent of overflow. -/
theorem increment_runs (word tmp : K) (hne : word ≠ tmp) (s : Stacks K) (a : Word w)
    (hx : s word = wordBits a) (ht : s tmp = []) :
    (increment word tmp).Runs (4*w+2) s (Function.update s word (wordBits (next a))) := by
  let y := (UnaryWord.incScan true (wordBits a)).1
  have hl : y.length = w := (UnaryWord.incScan_length ..).trans (length_wordBits _)
  have hv : TapeWord.value y < 2^w := hl ▸ TapeWord.value_lt y
  have hy : y = wordBits (next a) := by
    apply TapeWord.eq_of_length_value (hl.trans (length_wordBits _).symm)
    rw [← Nat.mod_eq_of_lt hv, TapeWord.value_wordBits, next, Fin.val_ofNat]
    have h := congrArg (· % (2^w)) (UnaryWord.incScan_value true (wordBits a))
    simpa only [length_wordBits, Nat.add_mul_mod_self_left, TapeWord.value_wordBits, Bool.toNat_true] using h
  have hr := small_runs (wordBits a)
  rw [length_wordBits, show (UnaryWord.incScan true (wordBits a)).1 = wordBits (next a) from hy] at hr
  have inj : Function.Injective (counters word tmp) := by
    intro i j he; cases i <;> cases j <;> simp_all [counters]
  apply small.runs_onPorts_framed inj hr
  · intro i; cases i <;> assumption
  · intro i; cases i <;> simp [counters, bank, hne.symm, ht]
  · intro k hk; exact Function.update_of_ne (Ne.symm (hk false)) ..

end TeamBurstProbeStep

end BorderVNP
end Computability
end OAI
