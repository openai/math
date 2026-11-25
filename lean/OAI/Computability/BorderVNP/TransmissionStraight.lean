import OAI.Computability.BorderVNP.TransmissionBit

/-! # Cost and register invariants for straight transmission paths -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- A bounded single-bit fragment may branch and probe shared words, but has no loops
and no private burst. -/
def Code.unitCostPath : Code → Bool
  | .whileLt .. | .call .. => false
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .choose a b => a.unitCostPath && b.unitCostPath
  | _ => true

/-- The fixed opcode slot count bounds the charged ticks of every successful loop-free,
burst-free path. -/
theorem Runs.cost_le_slots {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s t m mt es c} (run : Runs pub macros c s m es t mt) (hc : c.unitCostPath = true) :
    traceCost es ≤ c.slots := by
  induction run with
  | @atom c s m a t z bits atomic ha hb =>
    cases c <;> simp only [Code.isAtom,Code.unitCostPath] at atomic hc <;> try contradiction
    case binary op d x y =>
      simp only [Code.atom] at ha
      split at ha <;> simp [TeamRAM.Instr.action] at ha
      subst a; rfl
    all_goals simp [Code.atom, TeamRAM.Instr.action] at ha
    all_goals subst a; rfl
  | seq _ _ ih ih' =>
    obtain ⟨h,j⟩ := Bool.and_eq_true_iff.mp hc
    rw [Transmission.cost_append,Code.slots]
    exact Nat.add_le_add (ih h) (ih' j)
  | ifEq hr ih | ifLt hr ih | choose _ hr ih =>
    obtain ⟨h,j⟩ := Bool.and_eq_true_iff.mp hc
    have e := ih (by split <;> assumption)
    change 1 + _ ≤ 1 + _ + _
    unfold traceCost at e
    split at e <;> omega
  | whileDone | whileStep => contradiction

/-- Syntactic protection of the low registers, also allowing stores and binary choices. -/
def Code.preservesRange : Code → Bool
  | .constant d _ | .publicWord d _ | .copy d _ | .binary _ d _ _ | .load d _ => decide (16 < d.val)
  | .seq a b | .ifLt _ _ a b | .ifEq _ _ a b | .choose a b => a.preservesRange && b.preservesRange
  | .whileLt _ _ a => a.preservesRange
  | .call .. => false
  | _ => true

/-- A path whose only destinations are scratch registers preserves the range state,
including on a path with arbitrary loads, stores and private guesses. -/
theorem Runs.sameRange {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s t m mt es c} (run : Runs pub macros c s m es t mt) (hc : c.preservesRange = true) :
    Transmission.sameRange s t := by
  induction run with
  | @atom c s m a t z bits atomic ha hb =>
    cases c <;> simp only [Code.isAtom,Code.preservesRange] at atomic hc <;> try contradiction
    case binary op d x y =>
      simp only [Code.atom] at ha hb
      split at ha <;> rename_i he
      · simp [TeamRAM.Instr.action] at ha
      · simp [TeamRAM.Instr.action] at ha; subst a
        cases bits <;> simp [he,TeamRAM.Instr.advance,TeamRAM.previous] at hb
        rw [← hb.1]
        intro i hi
        exact Function.update_of_ne (by have hh : 16 < d.val := of_decide_eq_true hc; intro e; subst i; omega) ..
    all_goals simp [Code.atom,TeamRAM.Instr.action] at ha
    all_goals subst a
    all_goals cases bits <;> simp [Code.atom,TeamRAM.Instr.advance,TeamRAM.previous] at hb
    all_goals try (rw [← hb.1]; exact fun _ _ => rfl)
    all_goals rw [← hb.1]; intro i hi
    all_goals exact Function.update_of_ne (by have hh := of_decide_eq_true hc; intro e; subst i; omega) ..
  | seq _ _ ih jh =>
    obtain ⟨h,j⟩ := Bool.and_eq_true_iff.mp hc
    exact fun i hi => (jh j i hi).trans (ih h i hi)
  | ifEq _ ih | ifLt _ ih | choose _ _ ih =>
    obtain ⟨h,j⟩ := Bool.and_eq_true_iff.mp hc
    exact ih (by split <;> assumption)
  | whileDone => exact fun _ _ => rfl
  | whileStep _ _ _ ih jh => exact fun i hi => (jh hc i hi).trans (ih hc i hi)

end RoutingISA

end BorderVNP
end Computability
end OAI
