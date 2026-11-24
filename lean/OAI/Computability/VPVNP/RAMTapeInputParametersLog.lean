import OAI.Computability.VPVNP.RAMTapeWordSlice
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.Log

/-!
# Reading the ceiling binary logarithm from a padded word

After reversing the bit stack, skip the leading zeros. For each bit below
the leading one emit one mark. A final extra mark is needed exactly when
one of those lower bits was set.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.WordCeilLog

open TapeWord

/-- Labels for the padded word, its reversed copy, and the unary ceiling-log output. -/
inductive Port | word | tmp | out
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- States for reversing the word, skipping leading zeros, counting lower positions, and
rounding up if any lower bit is set. -/
inductive State
  | reverse | save (bit : Bool) | leading | lower (nonzero : Bool) | mark (nonzero : Bool)
  | extra | done
  deriving DecidableEq, Fintype

/-- Emit one unary mark per position below the highest set bit and one more if a lower bit is
set, giving the ceiling binary logarithm. -/
def code : StackCode Port State
  | .reverse => .pop .word fun b => b.elim .leading .save
  | .save b => .push .tmp b .reverse
  | .leading => .pop .tmp fun
      | none => .done
      | some false => .leading
      | some true => .lower false
  | .lower nz => .pop .tmp fun b => b.elim (if nz then .extra else .done) (fun v => .mark (nz || v))
  | .mark nz => .push .out true (.lower nz)
  | .extra => .push .out true .done
  | .done => .halt true

/-- Place the word, its temporary reversal, and accumulated output on the logarithm scanner’s
ports. -/
def store (word tmp out : List Bool) : Stacks Port
  | .word => word
  | .tmp => tmp
  | .out => out

private theorem write_store (w t o l : List Bool) (k : Port) :
    Function.update (store w t o) k l = match k with
      | .word => store l t o
      | .tmp => store w l o
      | .out => store w t l := by funext j; cases k <;> cases j <;> simp [store]

local macro "log_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, write_store])

private theorem reverse_run (x t out : List Bool) :
    StackRuns code (2*x.length+1) .reverse (store x t out) .leading (store [] (x.reverse ++ t) out) := by
  induction x generalizing t with
  | nil => log_step; exact .nil ..
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    log_step
    log_step
    exact ih (b :: t)

private theorem lower_run (x out : List Bool) (nz : Bool) :
    let extra := (nz || x.any id).toNat
    StackRuns code (2*x.length+1+extra) (.lower nz) (store [] x out) .done
      (store [] [] (List.replicate (x.length+extra) true ++ out)) := by
  induction x generalizing nz out with
  | nil =>
    cases nz <;> simp only [List.length_nil, List.any_nil, Bool.or_false, Bool.toNat_false,
      Bool.toNat_true, Nat.mul_zero, Nat.zero_add, Nat.add_zero, List.replicate_zero, List.nil_append,
      List.replicate_one, List.singleton_append]
    · log_step; exact .nil ..
    · log_step; log_step; exact .nil ..
  | cons b xs ih =>
    have h := ih (true :: out) (nz || b)
    have he : (nz || (b::xs).any id) = ((nz || b) || xs.any id) := by simp [Bool.or_assoc]
    dsimp only
    rw [he]
    simp only [List.length_cons, Nat.mul_succ, Nat.succ_add, List.replicate_succ']
    rw [List.append_assoc, List.singleton_append]
    rw [show (2*xs.length+(nz || b || xs.any id).toNat).succ.succ.succ =
      (2*xs.length+1+(nz || b || xs.any id).toNat)+1+1 by omega]
    log_step
    log_step
    exact h

/-- If the most significant bit is set, the ceiling logarithm counts the
bits below it and tests whether any of them is set. -/
theorem clog_leading_one (x : List Bool) :
    Nat.clog 2 (value ((true :: x).reverse)) = x.length + (x.any id).toNat := by
  have hx : value x.reverse = 0 ↔ x.any id = false := by
    induction x with
    | nil => simp [value]
    | cons b xs ih =>
      cases b <;> simp [List.reverse_cons, value_append, value, ih]
  have hlt : value x.reverse < 2^x.length := by simpa using value_lt x.reverse
  simp only [List.reverse_cons, value_append, List.length_reverse, value, Nat.mul_zero,
    Bool.toNat_true, Nat.add_zero, Nat.mul_one]
  cases h : x.any id with
  | false => simp [hx.mpr h, Nat.clog_pow 2 _ (by decide)]
  | true =>
    have hp : 0 < value x.reverse := Nat.pos_of_ne_zero (fun he => by rw [hx.mp he] at h; contradiction)
    simp only [Bool.toNat_true]
    apply le_antisymm
    · apply Nat.clog_le_of_le_pow
      rw [pow_succ]
      omega
    · apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
      omega

private theorem leading_run (x out : List Bool) :
    ∃ t ≤ 2*x.length+2, StackRuns code t .leading (store [] x out) .done
      (store [] [] (List.replicate (Nat.clog 2 (value x.reverse)) true ++ out)) := by
  induction x with
  | nil =>
    refine ⟨1, by decide, ?_⟩
    simp only [List.reverse_nil, value, Nat.clog_zero_right, List.replicate_zero, List.nil_append]
    log_step
    exact .nil ..
  | cons b xs ih =>
    cases b with
    | false =>
      obtain ⟨t, ht, run⟩ := ih
      refine ⟨t+1, by simp only [List.length_cons, Nat.mul_succ]; omega, ?_⟩
      simp only [List.reverse_cons, value_append, value, Bool.toNat_false, Nat.mul_zero,
        Nat.add_zero]
      log_step
      exact run
    | true =>
      let k := (xs.any id).toNat
      have hk : k ≤ 1 := by unfold k; cases xs.any id <;> decide
      refine ⟨(2*xs.length+1+k)+1, by simp only [List.length_cons, Nat.mul_succ]; omega, ?_⟩
      rw [clog_leading_one]
      log_step
      simpa only [Bool.false_or] using lower_run xs out false

/-- Read every word, including zero and words with high padding, in linear time. -/
theorem runs (x out : List Bool) :
    ∃ t ≤ 4*x.length+3, StackRuns code t .reverse (store x [] out) .done
      (store [] [] (List.replicate (Nat.clog 2 (value x)) true ++ out)) := by
  obtain ⟨t, ht, run⟩ := leading_run x.reverse out
  have h := reverse_run x [] out
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at ht run h
  exact ⟨_, by omega, h.trans run⟩

end RAMTape.WordCeilLog

end VPVNP
end Computability
end OAI
