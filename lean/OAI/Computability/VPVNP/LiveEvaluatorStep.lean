import OAI.Computability.VPVNP.LiveEvaluatorEncoding
import Mathlib.Tactic.FinCases
import OAI.Computability.VPVNP.VerifierMachineSimulation
import OAI.Computability.VPVNP.RAMTapeSpaceTravel

/-!
# One finite-window evaluator transition in a live group

Each output cell reads a single offset from the previous window. Two
additional blank checks, immediately outside the new window, detect any
loss of nonblank tape data. Halts carry the unique canonical state code.
One choice bit selects a table slot, so equal instructions in a branching
row remain distinguishable.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorStep

open UniversalMachine LiveEvaluatorEncoding RAMTape

variable {M extra : ℕ}

theorem updateTape_nth (t : Turing.Tape Symbol) (write move : Symbol) (j : ℤ) :
    (updateTape t write move).nth j =
      if j + moveDelta move = 0 then write else t.nth (j + moveDelta move) := by
  fin_cases move <;> simp [updateTape, sub_eq_add_neg] <;> rfl

/-- Symbol at signed displacement `j` after writing at the old head and moving. -/
def updatedCell (t : TapeWindow M) (write move : Symbol) (j : ℤ) : Symbol :=
  let old := j + moveDelta move
  if old = 0 then write else t.read old

theorem updatedCell_eq_nth (t : TapeWindow M) (write move : Symbol) (j : ℤ) :
    updatedCell t write move j = (updateTape t.toTape write move).nth j := by
  rw [updateTape_nth, t.toTape_nth]
  rfl

/-- The only two exterior positions which can receive a nonblank cell. -/
def boundaryBlank (t : TapeWindow M) (write move : Symbol) : Bool :=
  decide (updatedCell t write move (-(M : ℤ) - 1) = 0 ∧ updatedCell t write move (M + 1) = 0)

theorem boundaryBlank_iff (t : TapeWindow M) (write move : Symbol) :
    boundaryBlank t write move = true ↔ TapeFits M (updateTape t.toTape write move) := by
  simp only [boundaryBlank, decide_eq_true_eq, updatedCell_eq_nth]
  constructor
  · intro h j hj
    by_cases hl : j = -(M : ℤ) - 1
    · exact hl ▸ h.1
    by_cases hr : j = (M : ℤ) + 1
    · exact hr ▸ h.2
    have hd := delta_range move
    have hfar : j + moveDelta move < -(M : ℤ) ∨ (M : ℤ) < j + moveDelta move := by omega
    rw [updateTape_nth, ite_eq_right (by omega)]
    exact t.toTape_fits _ hfar
  · intro h
    exact ⟨h _ (by omega), h _ (by omega)⟩

/-- The finite head-relative tape window resulting from the proposed head write and movement. -/
def updatedWindow (t : TapeWindow M) (write move : Symbol) : TapeWindow M :=
  ⟨fun i => updatedCell t write move ((i.val : ℤ) - M)⟩

theorem updatedWindow_eq (t : TapeWindow M) (write move : Symbol) :
    updatedWindow t write move = TapeWindow.ofTape M (updateTape t.toTape write move) := by
  apply TapeWindow.ext
  funext i
  exact updatedCell_eq_nth t write move _

/-- Check a selected instruction. The two boundary reads are necessary only
when its target is running, since the representation discards both tapes on a halt. -/
def advanceCode (s : ConfigWindow extra M) (a : Instruction extra) : Option (Code extra M) :=
  if ha : a.target.val = 1 then some .accepted
  else if hr : a.target.val = 0 then some .rejected
  else if boundaryBlank s.firstTape a.firstSymbol a.firstMove &&
      boundaryBlank s.secondTape a.secondSymbol a.secondMove then
    some (.running ⟨a.target, updatedWindow s.firstTape a.firstSymbol a.firstMove,
      updatedWindow s.secondTape a.secondSymbol a.secondMove⟩ (by change 2 ≤ a.target.val; omega))
  else none

/-- Read the fixed row table at the state and the two current symbols. -/
def row (p : Program) (s : ConfigWindow p.extra M) : Branches p.extra :=
  p.rows[(s.state.val - 2) * 9 + (s.firstTape.cells (windowCenter M)).val * 3 +
    (s.secondTape.cells (windowCenter M)).val]?.getD .stop

theorem row_eq (p : Program) (s : ConfigWindow p.extra M) : row p s = branches p s.toConfig := rfl

/-- Advance a cut code using one row-selection bit, handling carried halts, missing slots, and
the finite-window transition check. -/
def nextCode (p : Program) (s : Code p.extra M) (bit : Bool) : Option (Code p.extra M) :=
  match s with
  | .accepted => some (if bit then .rejected else .accepted)
  | .rejected => some .rejected
  | .running c _ =>
    match chosenInstruction (row p c) bit with
    | none => some .rejected
    | some a => advanceCode c a

private theorem toState_injective : Function.Injective (Code.toState (extra := extra) (M := M)) :=
  fun _ _ h => (codeEquiv extra M).injective (Subtype.ext h)

private theorem code_eq_state (s z : Code extra M) : s = z ↔ z.toState = s.toState :=
  ⟨fun h => h ▸ rfl, fun h => (toState_injective h).symm⟩

/-- A transition emits precisely the bounded representation of the true
successor. If it clips a tape, no outgoing code passes the transition test. -/
theorem advanceCode_iff (s : ConfigWindow extra M) (a : Instruction extra) (z : Code extra M) :
    advanceCode s a = some z ↔ z.toState = EvaluatorTail.canonical (advance s.toConfig a) := by
  by_cases ha : a.target.val = 1
  · simpa [advanceCode, ha, EvaluatorTail.canonical, advance, Code.toState] using code_eq_state Code.accepted z
  by_cases hr : a.target.val = 0
  · simpa [advanceCode, hr, EvaluatorTail.canonical, advance, Code.toState] using code_eq_state Code.rejected z
  let c := advance s.toConfig a
  have hcanon : EvaluatorTail.canonical c = .running c := by simp [c, EvaluatorTail.canonical, advance, ha, hr]
  rw [show advance s.toConfig a = c from rfl, hcanon]
  by_cases hf : ConfigFits M c
  · have h₁ := hf.1
    have h₂ := hf.2
    have hb₁ := (boundaryBlank_iff s.firstTape a.firstSymbol a.firstMove).mpr h₁
    have hb₂ := (boundaryBlank_iff s.secondTape a.secondSymbol a.secondMove).mpr h₂
    simp [advanceCode, ha, hr, hb₁, hb₂, updatedWindow_eq]
    let v : Code extra M := .running (ConfigWindow.ofConfig M c) (by change 2 ≤ a.target.val; omega)
    change v = z ↔ _
    have hv : v.toState = EvaluatorTail.State.running c := by
      change EvaluatorTail.State.running ((ConfigWindow.ofConfig M c).toConfig) = _
      rw [ConfigWindow.toConfig_ofConfig _ hf]
    exact ⟨fun h => h ▸ hv, fun h => toState_injective (hv.trans h.symm)⟩
  · have hb : ¬ (boundaryBlank s.firstTape a.firstSymbol a.firstMove &&
        boundaryBlank s.secondTape a.secondSymbol a.secondMove) = true := by
      intro h
      rw [Bool.and_eq_true] at h
      exact hf ⟨(boundaryBlank_iff ..).mp h.1, (boundaryBlank_iff ..).mp h.2⟩
    simp [advanceCode, ha, hr, hb]
    intro hz
    have h := z.toState_fits
    rw [hz] at h
    exact hf h.2

theorem nextCode_iff (p : Program) (s z : Code p.extra M) (bit : Bool) :
    nextCode p s bit = some z ↔ z.toState = EvaluatorTail.step p s.toState bit := by
  cases s with
  | accepted =>
    cases bit
    · exact (Option.some.injEq ..).to_iff.trans (code_eq_state Code.accepted z)
    · exact (Option.some.injEq ..).to_iff.trans (code_eq_state Code.rejected z)
  | rejected => exact (Option.some.injEq ..).to_iff.trans (code_eq_state Code.rejected z)
  | running c hc =>
    have ha : c.toConfig.state.val ≠ 1 := by change c.state.val ≠ 1; omega
    have hr : c.toConfig.state.val ≠ 0 := by change c.state.val ≠ 0; omega
    simp only [nextCode, row_eq, Code.toState, EvaluatorTail.step, choiceStep, ha, hr, ite_false]
    cases hb : branches p c.toConfig <;> cases bit <;>
      first | exact advanceCode_iff .. |
        simpa [chosenInstruction, EvaluatorTail.canonical, reject, Code.toState] using code_eq_state Code.rejected z

end LiveEvaluatorStep

end VPVNP
end Computability
end OAI
