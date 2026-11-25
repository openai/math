import OAI.Computability.BorderVNP.RoutingISARuns

/-! # Register preservation across structured native RAM executions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- A fixed assembly fragment never assigns to this register on either branch or inside a loop. -/
def Code.keeps (k : Reg) : Code → Bool
  | .constant d _ | .publicWord d _ | .copy d _ | .binary _ d _ _ | .load d _ => decide (k ≠ d)
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .choose a b => a.keeps k && b.keeps k
  | .whileLt _ _ a => a.keeps k
  | _ => true

private theorem atom_keep {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s t : Bank w} {bs : List Bool} {vs : List (Word w)} {z : TeamRAM.Sign}
    {k : Reg} (keep : c.keeps k = true) (ok : (c.atom pub macros s).advance bs vs = some (t,z)) :
    t k = s k := by
  cases c <;> simp only [Code.keeps, decide_eq_true_eq] at keep <;> simp only [Code.atom] at ok
  case binary op d x y =>
    split at ok
    · simp [TeamRAM.Instr.advance] at ok
    · cases bs <;> cases vs <;> simp [TeamRAM.Instr.advance] at ok
      exact ok.1 ▸ Function.update_of_ne keep ..
  case load d a =>
    cases vs with
    | nil => cases bs <;> simp [TeamRAM.Instr.advance] at ok
    | cons v vs => cases vs <;> cases bs <;> simp [TeamRAM.Instr.advance] at ok
                   exact ok.1 ▸ Function.update_of_ne keep ..
  case store a v =>
    cases vs with
    | nil => cases bs <;> simp [TeamRAM.Instr.advance] at ok
    | cons x xs => cases xs <;> cases bs <;> simp [TeamRAM.Instr.advance] at ok
                   exact congrFun ok.1.symm k
  case call j a l =>
    simp only [TeamRAM.Instr.advance] at ok
    split at ok
    · obtain ⟨_,_,he⟩ := Option.map_eq_some_iff.mp ok
      exact congrFun (congrArg Prod.fst he).symm k
    · contradiction
  all_goals
    cases bs <;> cases vs <;> simp [TeamRAM.Instr.advance] at ok
  all_goals first | exact congrFun ok.1.symm k | exact ok.1 ▸ Function.update_of_ne keep ..

/-- Every genuine run preserves registers that are never destinations in the assembled code. -/
theorem Runs.keepsReg {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (run : Runs pub macros c s m es t mt) {k : Reg}
    (keep : c.keeps k = true) : t k = s k := by
  induction run with
  | atom _ _ advance => exact atom_keep keep advance
  | seq _ _ h₁ h₂ =>
    obtain ⟨h₁',h₂'⟩ := Bool.and_eq_true_iff.mp keep
    exact (h₂ h₂').trans (h₁ h₁')
  | ifEq _ ih | ifLt _ ih | choose _ _ ih =>
    obtain ⟨yes,no⟩ := Bool.and_eq_true_iff.mp keep
    apply ih
    split <;> assumption
  | whileDone => rfl
  | whileStep _ _ _ ih₁ ih₂ => exact (ih₂ keep).trans (ih₁ keep)

end RoutingISA

end BorderVNP
end Computability
end OAI
