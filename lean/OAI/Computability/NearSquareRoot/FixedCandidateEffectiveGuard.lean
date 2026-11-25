import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyTally

/-! # Effective width tests and the common finite-input fallback -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code Space CommonRegisters GeneratorSyntax EffectiveBoundedTask Filter
open private fastHome capS from OAI.Computability.IntegerMultiplication.Foundation
open private input_count from OAI.Computability.NearSquareRoot.FixedCandidateGuard

variable {P : Type} [Primcodable P]

/-- The threshold is computed while emitting the candidate program. The
resulting file performs a linear scan, preserving the operands under its flag. -/
private theorem effective_tag (K : P → ℕ) (hK : Computable K) :
    Family (fun _ (i : MultiplicationInput) => i.width) (fun _ i => i.width)
      (fun _ i => send i.operands) (fun p i => .fork (.atom (tags (K p) i)) (send i.operands)) := by
  let flag (p : P) (x : Interface.Pair) := (Iter.small (x.1,tally (K p)),x)
  obtain ⟨R,hR,hF,hS⟩ : ∃ R, 3 ≤ R ∧ RegisterWitness.Easy R (Prod.fst (β := Bits.Word) (α := Bits.Word)) ∧
      RegisterWitness.Easy R (Iter.small (X := Bool) (Y := Unit)) := by
    exact ((eventually_ge_atTop (3:ℕ)).and ((RegisterSelect.easy_eventually Easy.fst).and
      (RegisterSelect.easy_eventually Iter.small_easy))).exists
  have scan : KernelEffectiveFamily.Family R flag :=
    (((KernelEffectiveFamily.Family.fixed hF).pair hR (KernelEffectiveFamily.Family.tally (by omega) K hK)).comp
      (KernelEffectiveFamily.Family.fixed hS)).pair hR KernelEffectiveFamily.Family.identity
  obtain ⟨cmd,he,h⟩ := scan
  refine ⟨cmd,R,he,by omega,fun p => ⟨(h p).1,?_⟩⟩
  have rr : Runs (cmd p) (fun i : MultiplicationInput => size i.operands)
      (fun i => (send i.operands).count+size i.operands)
      (fun i => send i.operands) (fun i => send (flag p i.operands)) := by
    obtain ⟨C,hc⟩ := (h p).2
    exact Runs.of_time ⟨C,fun i => hc i.operands⟩
  have eq (i : MultiplicationInput) : flag p i.operands =
      (tags (K p) i, i.operands) := by simp [flag,Iter.small,tags,n0,v,MultiplicationInput.operands]
  simp_rw [eq] at rr
  apply rr.bound 5 9
  · intro i
    change (send i.operands).count+1 ≤ 5*(i.width+1)
    rw [input_count]
    omega
  · intro i
    change (send i.operands).count+(send i.operands).count+1 ≤ 9*(i.width+1)
    rw [input_count]
    omega

/-- The polynomial-time ordinary multiplier has one syntax file for all
thresholds. Its finite-domain clock constant may depend on the outer index. -/
private theorem effective_short (K : P → ℕ) :
    Family (fun p (_ : shortS (K p)) => 0) (fun _ i => MultiplicationInput.width i.val)
      (fun _ i => send (MultiplicationInput.operands i.val))
      (fun _ i => send (Lea.answer (MultiplicationInput.operands i.val))) := by
  obtain ⟨t,⟨degree,A,hA⟩,c,C,hc⟩ := fastHome
  apply Family.fixed_run c
  intro p
  let M := A*(8*(K p+1)+1)^degree
  have clock (i : shortS (K p)) : t (v i.val) ≤ M :=
    (hA _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ (capS (K p) i)) _))
  have rr : Runs c (fun i : shortS (K p) => t (v i.val))
      (fun i => (send (v i.val)).count+t (v i.val))
      (fun i => send (v i.val)) (fun i => send (Lea.answer (v i.val))) :=
    Runs.of_time ⟨C,fun i => hc (v i.val)⟩
  apply rr.bound (M+1) (M+5)
  · intro i
    simpa using Nat.succ_le_succ (clock i)
  · intro i
    change (send (MultiplicationInput.operands i.val)).count + t (v i.val) + 1 ≤ _
    rw [input_count]
    have hh := clock i
    have room := Nat.mul_le_mul_left (M+5) (show 1 ≤ MultiplicationInput.width i.val+1 by omega)
    rw [Nat.mul_one] at room
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
    omega

/-- Add a computably generated threshold guard to each effective large-input
file. All arithmetic and branch instructions share one fixed register cutoff. -/
theorem effective_all_widths (K : P → ℕ) (hK : Computable K) (T : P → ℕ → ℕ)
    (fast : Family (fun p (i : LargeInput (K p)) => T p i.val.width) (fun _ i => i.val.width)
      (fun _ i => send i.val.operands) (fun _ i => send (Lea.answer i.val.operands))) :
    Family (fun p (i : MultiplicationInput) => i.width+T p i.width) (fun _ i => 21*i.width)
      (fun _ i => send i.operands) (fun _ i => send (Lea.answer i.operands)) := by
  let t (p : P) (i : MultiplicationInput) := i.width + T p i.width
  let s (_ : P) (i : MultiplicationInput) := 21*i.width
  have large := fast.on (fun p (i : longS (K p)) =>
    (⟨i.val,Nat.le_of_not_gt (of_decide_eq_false i.property)⟩ : LargeInput (K p)))
  have act := Family.control (t := t) (s := fun _ (i : MultiplicationInput) => i.width)
    (u := fun _ (i : MultiplicationInput) => send i.operands) (v := fun _ i => send (Lea.answer i.operands))
    (fun p (i : MultiplicationInput) => tags (K p) i)
    (large.mono (fun p i => by dsimp [t]; omega) (fun _ _ => le_rfl))
    ((effective_short K).mono (fun _ _ => Nat.zero_le _) (fun _ _ => le_rfl))
  change Family t s _ _
  apply Family.sequence (v := fun p (i : MultiplicationInput) => .fork (.atom (tags (K p) i)) (send i.operands))
  · exact (effective_tag K hK).mono (fun _ _ => Nat.le_add_right ..) (fun _ i => by change i.width ≤ 21*i.width; omega)
  · apply act.mono (fun _ _ => le_rfl)
    intro p i
    change i.width + (send i.operands).count ≤ 21*i.width
    rw [input_count]
    have := i.property
    change 1 ≤ i.width at this
    omega

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
