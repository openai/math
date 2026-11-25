import OAI.Computability.BorderVNP.DiagonalTallyRAMCode

/-! # Ordinary ticks in the tally stage

Tally assembly uses neither signed returns, private calls nor branch guesses.
Consequently every genuine tick contributes one positive factor and costs exactly
one tick, including each individual shared word probe.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA

/-- Only ordinary deterministic operations occur on either side of every control branch. -/
def ordinary : Code → Bool
  | .sign _ | .call .. | .choose .. => false
  | .seq a b | .ifLt _ _ a b | .ifEq _ _ a b => ordinary a && ordinary b
  | .whileLt _ _ body => ordinary body
  | _ => true

private def ordinaryInstruction {w : ℕ} {S : Type*} : TeamRAM.Instr w S → Prop
  | .accept | .reject | .localStep _ .plus | .load .. | .store .. => True
  | _ => False

private theorem ordinary_atom {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s t : Bank w} {act bs words sign} (h : ordinary c = true)
    (ha : (c.atom pub mac s).action = some act)
    (hb : (c.atom pub mac s).advance bs words = some (t,sign)) :
    bs = [] ∧ sign = .plus ∧ act.extra = 0 := by
  have ok : ordinaryInstruction (c.atom pub mac s) := by
    cases c <;> try contradiction
    all_goals dsimp only [Code.atom]
    all_goals first | trivial | (split <;> trivial)
  generalize hh : c.atom pub mac s = i at ok ha hb
  cases i with
  | accept | reject => cases ha
  | call | choose => contradiction
  | localStep next z =>
    cases z <;> try contradiction
    cases ha
    cases bs <;> cases words <;> simp [TeamRAM.Instr.advance] at hb
    rcases hb with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,rfl⟩
  | load | store =>
    cases ha
    cases bs <;> cases words <;> simp [TeamRAM.Instr.advance] at hb
    all_goals rename_i tail; cases tail <;> simp at hb
    all_goals rcases hb with ⟨rfl,rfl⟩; exact ⟨rfl,rfl,rfl⟩

/-- On any ordinary assembly run, every event costs one native tick and has sign +1. -/
theorem ordinary_run {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s t : Bank w} {m mt : Memory w} {es} (hc : ordinary c = true)
    (r : Runs pub mac c s m es t mt) :
    ∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0 := by
  induction r with
  | atom _ ha hb =>
    obtain ⟨rfl,rfl,hex⟩ := ordinary_atom hc ha hb
    simp [hex]
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hc
    exact fun e he => (List.mem_append.mp he).elim (ih₁ h₁ e) (ih₂ h₂ e)
  | ifEq _ ih | ifLt _ ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hc
    have hh := ih (by split <;> assumption)
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact ⟨rfl,rfl,rfl⟩
    · exact hh e h
  | choose => contradiction
  | whileDone => simp [tick,TeamTranscript.Action.extra]
  | whileStep _ _ _ ih₁ ih₂ =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact ⟨rfl,rfl,rfl⟩
    · exact (List.mem_append.mp h).elim (ih₁ hc e) (ih₂ hc e)

/-- The chronological trace length equals the full burst-accounting cost on such a run. -/
theorem ordinary_cost {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s t : Bank w} {m mt : Memory w} {es} (hc : ordinary c = true)
    (r : Runs pub mac c s m es t mt) : traceCost es = es.length := by
  have h := ordinary_run hc r
  clear hc r
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := (h e List.mem_cons_self).2.2
    simp only [traceCost, VPVNP.RAMBuckets.cost, he, Nat.add_zero, List.length_cons]
    change 1+traceCost es = _
    rw [ih (fun x hx => h _ (.tail _ hx))]
    omega

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
