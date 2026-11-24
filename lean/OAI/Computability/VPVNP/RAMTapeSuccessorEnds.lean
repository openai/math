import OAI.Computability.VPVNP.RAMTapeWord
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype

/-!
# Detecting the two ends of the site chain

A site has an outgoing edge when a bit in its address is zero. It has an
incoming edge when a bit is one. The scan saves and restores the address and
returns both edge-presence flags in finite control.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorEnds

open TapeWord BurstRAM

/-- States for scanning and restoring the site address while recording whether outgoing and
incoming edges exist. -/
inductive State where
  | read (outgoing incoming : Bool)
  | save (outgoing incoming bit : Bool)
  | restore (outgoing incoming : Bool)
  | put (outgoing incoming bit : Bool)
  | done (outgoing incoming : Bool)
  deriving DecidableEq, Fintype

variable {K : Type*}

/-- The control scans a site address once, then transfers its bits back. -/
def code (src tmp : K) : StackCode K State
  | .read o i => .pop src fun b => b.elim (.restore o i) fun x => .save (o || !x) (i || x) x
  | .save o i x => .push tmp x (.read o i)
  | .restore o i => .pop tmp fun b => b.elim (.done o i) (.put o i)
  | .put o i x => .push src x (.restore o i)
  | .done _ _ => .halt true

theorem any_zero (xs : List Bool) : xs.any (!·) = decide (value xs + 1 < 2 ^ xs.length) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have hb := value_lt xs
    rw [List.any_cons, ih]
    apply Bool.eq_iff_iff.mpr
    cases b <;> simp [value, pow_succ] <;> omega

theorem any_one (xs : List Bool) : xs.any id = decide (0 < value xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [List.any_cons, ih]
    apply Bool.eq_iff_iff.mpr
    cases b <;> simp [value]

variable [DecidableEq K] (src tmp : K)

private def bank (s : Stacks K) (x t : List Bool) : Stacks K :=
  Function.update (Function.update s tmp t) src x

private theorem bank_src (s : Stacks K) (x t : List Bool) : bank src tmp s x t src = x := by
  simp [bank]

private theorem bank_tmp (h : src ≠ tmp) (s : Stacks K) (x t : List Bool) :
    bank src tmp s x t tmp = t := by
  simp [bank, Function.update_of_ne (Ne.symm h)]

private theorem write_src (s : Stacks K) (x t v : List Bool) :
    Function.update (bank src tmp s x t) src v = bank src tmp s v t := by
  simp only [bank, Function.update_idem]

private theorem write_tmp (h : src ≠ tmp) (s : Stacks K) (x t v : List Bool) :
    Function.update (bank src tmp s x t) tmp v = bank src tmp s x v := by
  rw [bank, Function.update_comm h, Function.update_idem, bank]

local macro "end_step" h:term : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [bank_src, bank_tmp _ _ $h, List.head?_cons, List.tail_cons, List.head?_nil,
    List.tail_nil, Option.elim_some, Option.elim_none, write_src, write_tmp _ _ $h])

private theorem read_run (h : src ≠ tmp) (s : Stacks K) (x t : List Bool) (o i : Bool) :
    StackRuns (code src tmp) (2 * x.length + 1) (.read o i) (bank src tmp s x t)
      (.restore (o || x.any (!·)) (i || x.any id)) (bank src tmp s [] (x.reverse ++ t)) := by
  induction x generalizing t o i with
  | nil =>
    simp only [List.any_nil, Bool.or_false, List.reverse_nil, List.nil_append]
    end_step h
    exact .nil ..
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.any_cons, id_eq, ← Bool.or_assoc]
    end_step h
    end_step h
    exact ih _ _ _

private theorem restore_run (h : src ≠ tmp) (s : Stacks K) (x t : List Bool) (o i : Bool) :
    StackRuns (code src tmp) (2 * t.length + 1) (.restore o i) (bank src tmp s x t)
      (.done o i) (bank src tmp s (t.reverse ++ x) []) := by
  induction t generalizing x with
  | nil =>
    end_step h
    exact .nil ..
  | cons b t ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    end_step h
    end_step h
    exact ih _

/-- The entire bank is restored, including the address. The empty address
returns two false flags, as required for the single-site chain. -/
theorem run (h : src ≠ tmp) (s : Stacks K) (ht : s tmp = []) :
    StackRuns (code src tmp) (4 * (s src).length + 2) (.read false false) s
      (.done (decide (value (s src) + 1 < 2 ^ (s src).length)) (decide (0 < value (s src)))) s := by
  let xs := s src
  have hf := read_run src tmp h s xs [] false false
  have hr := restore_run src tmp h s [] xs.reverse (xs.any (!·)) (xs.any id)
  have hs : bank src tmp s xs [] = s := by
    simp [bank, xs, ← ht]
  simp only [Bool.false_or, List.append_nil, List.length_reverse, List.reverse_reverse, hs] at hf hr
  have hc := hf.trans hr
  rw [any_zero, any_one] at hc
  convert hc using 1
  dsimp [xs]
  omega

theorem word_run {d : ℕ} (h : src ≠ tmp) (s : Stacks K) (v : Word d)
    (hv : s src = wordBits v) (ht : s tmp = []) :
    StackRuns (code src tmp) (4 * d + 2) (.read false false) s
      (.done (decide (v.val + 1 < 2 ^ d)) (decide (0 < v.val))) s := by
  simpa only [hv, length_wordBits, value_wordBits] using run src tmp h s ht

end RAMTape.SuccessorEnds

end VPVNP
end Computability
end OAI
