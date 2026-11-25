import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Choice-free, positive traces of the native scheduling instructions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- An ordinary unsigned fragment has no private calls, binary choices, or sign operations. -/
def Code.unsigned : Code → Bool
  | .sign .. | .call .. | .choose .. => false
  | .seq a b | .ifLt _ _ a b | .ifEq _ _ a b => a.unsigned && b.unsigned
  | .whileLt _ _ a => a.unsigned
  | _ => true

private theorem atom_positive {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s t : Bank w} {bs : List Bool} {v : List (Word w)} {z : TeamRAM.Sign}
    (hc : c.unsigned = true) (ha : (c.atom pub macros s).advance bs v = some (t,z)) :
    bs = [] ∧ z = .plus := by
  cases c with
  | binary op d x y =>
    by_cases h : (op = .div ∨ op = .mod) ∧ s y = 0
    · simp only [Code.atom, ite_eq_left h, TeamRAM.Instr.advance, reduceCtorEq] at ha
    · simp only [Code.atom, ite_eq_right h] at ha
      cases bs <;> cases v <;> simp_all [TeamRAM.Instr.advance]
  | load | store =>
    cases bs <;> cases v with
    | nil => simp_all [Code.atom, TeamRAM.Instr.advance]
    | cons v vs => cases vs <;> simp_all [Code.atom, TeamRAM.Instr.advance]
  | _ => cases bs <;> cases v <;> simp_all [Code.unsigned, Code.atom, TeamRAM.Instr.advance]

/-- Every recorded event in a successfully executed unsigned program consumes no
choices and contributes positive sign. This includes all loop guards. -/
theorem Runs.unsigned_events {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (r : Runs pub macros c s m es t mt) (hc : c.unsigned = true) :
    ∀ e ∈ es, e.choices = [] ∧ e.sign = .plus := by
  induction r with
  | atom _ _ ha =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact atom_positive hc ha
  | seq _ _ ih ih' =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hc
    exact fun e he => (List.mem_append.mp he).elim (ih hl e) (ih' hr e)
  | ifLt _ ih | ifEq _ ih =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hc
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨rfl,rfl⟩
    · exact ih (by split <;> assumption) e he
  | choose => contradiction
  | whileDone =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact ⟨rfl,rfl⟩
  | whileStep _ _ _ ih ih' =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨rfl,rfl⟩
    · exact (List.mem_append.mp he).elim (ih hc e) (ih' hc e)

/-- The scheduling program has only deterministic unsigned opcodes. -/
theorem scheduleTable_unsigned : scheduleTable.unsigned = true := by decide

end RoutingISA

end BorderVNP
end Computability
end OAI
