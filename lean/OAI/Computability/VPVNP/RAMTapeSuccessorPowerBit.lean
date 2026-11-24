import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeWordSlice

/-! # Writing a power of two into a fixed-width little-endian word -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorPowerBit

open BurstRAM TapeWord

/-- Stacks for the unary exponent, destination word, and saved zero bits. -/
inductive Port where | exponent | word | tmp
  deriving DecidableEq
instance : Fintype Port := derive_fintype% _

/-- Control states for skipping low bits, setting the power-of-two bit, and restoring the lower
zeros. -/
inductive State where | scan | skip | save | set | putOne | restore | putZero | done | reject
  deriving DecidableEq
instance : Fintype State := derive_fintype% _

/-- Consume the unary exponent, write a one at that bit position, and fill the lower positions
with zeros, rejecting if the word is too short. -/
def code : StackCode Port State
  | .scan => .pop .exponent fun b ↦ b.elim .set (fun _ ↦ .skip)
  | .skip => .pop .word fun b ↦ b.elim .reject (fun _ ↦ .save)
  | .save => .push .tmp false .scan
  | .set => .pop .word fun b ↦ b.elim .reject (fun _ ↦ .putOne)
  | .putOne => .push .word true .restore
  | .restore => .pop .tmp fun b ↦ b.elim .done (fun _ ↦ .putZero)
  | .putZero => .push .word false .restore
  | .done => .halt true
  | .reject => .halt false

/-- Initialize the exponent as unary marks and the scratch stack as zeros alongside the
supplied word bits. -/
def bank (exp : ℕ) (word : List Bool) (tmp : ℕ) : Stacks Port
  | .exponent => List.replicate exp true
  | .word => word
  | .tmp => List.replicate tmp false

private def frame (exp word tmp : List Bool) : Stacks Port
  | .exponent => exp
  | .word => word
  | .tmp => tmp

private theorem write_frame (e w t xs : List Bool) (j : Port) :
    Function.update (frame e w t) j xs =
      match j with
      | .exponent => frame xs w t
      | .word => frame e xs t
      | .tmp => frame e w xs := by funext i; cases i <;> cases j <;> rfl

local macro "power_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [frame, write_frame, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_none, Option.elim_some])

private theorem forward (k t : ℕ) (suffix : List Bool) :
    StackRuns code (3*k+1) .scan
      (frame (List.replicate k true) (List.replicate k false ++ suffix) (List.replicate t false))
      .set (frame [] suffix (List.replicate (k+t) false)) := by
  induction k generalizing t with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add, Nat.mul_zero]
    power_step
    exact .nil ..
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.mul_succ, Nat.add_assoc]
    power_step
    power_step
    power_step
    simpa [List.replicate_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih (t+1)

private theorem backward (k : ℕ) (bits : List Bool) :
    StackRuns code (2*k+1) .restore (frame [] bits (List.replicate k false))
      .done (frame [] (List.replicate k false ++ bits) []) := by
  induction k generalizing bits with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    power_step
    exact .nil ..
  | succ k ih =>
    rw [List.replicate_succ, Nat.mul_succ]
    power_step
    power_step
    rw [← List.replicate_succ, List.replicate_succ', List.append_assoc, List.singleton_append]
    exact ih (false::bits)

theorem run (k w : ℕ) (hk : k < w) :
    StackRuns code (5*k+4) .scan (bank k (List.replicate w false) 0) .done
      (bank 0 (BurstRAM.wordBits (⟨2^k, Nat.pow_lt_pow_right (by decide) hk⟩ : Word w)) 0) := by
  let suffix := List.replicate (w-(k+1)) false
  have hf := forward k 0 (false :: suffix)
  have he : List.replicate k false ++ false :: suffix = List.replicate w false := by
    rw [show false :: suffix = List.replicate (w-(k+1)+1) false from (List.replicate_succ ..).symm,
      ← List.replicate_add, show k + (w-(k+1)+1) = w by omega]
  rw [he, Nat.add_zero] at hf
  have hm : StackRuns code 2 .set (frame [] (false::suffix) (List.replicate k false))
      .restore (frame [] (true::suffix) (List.replicate k false)) := by
    power_step
    power_step
    exact .nil ..
  have hbits : List.replicate k false ++ true :: suffix =
      BurstRAM.wordBits (⟨2^k, Nat.pow_lt_pow_right (by decide) hk⟩ : Word w) := by
    apply eq_of_length_value
    · simp [suffix]; omega
    · simp [value_append, value, suffix, value_wordBits]
  rw [← hbits, show 5*k+4 = (3*k+1)+2+(2*k+1) by omega]
  exact (hf.trans hm).trans (backward k _)

/-- Install the bit-setting instruction table on the caller's stacks, entering at the exponent
scan. -/
def routine {K : Type} (ports : Port → K) : FiniteRoutine K :=
  FiniteRoutine.ofStackCode code ports .scan (· == .done)

end RAMTape.SuccessorPowerBit

end VPVNP
end Computability
end OAI
