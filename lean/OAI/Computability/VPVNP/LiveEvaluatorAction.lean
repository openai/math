import OAI.Computability.VPVNP.LiveEvaluatorRAMCell
import OAI.Computability.VPVNP.LiveEvaluatorRAMDispatch

/-!
# Successful live evaluator instructions

The preparing call chooses an instruction and publishes five words. A carried
accept uses one all-zero-motion instruction. The two scheduled tape scans
check the proposed target. Together these checks characterize exactly the
nonrejecting successors of the bounded evaluator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAction

open UniversalMachine LiveEvaluatorEncoding LiveEvaluatorStep

variable {M extra : ℕ}

/-- The five scratch fields written when carrying an accepting halt. -/
def carry (extra : ℕ) : Instruction extra :=
  ⟨⟨1, by omega⟩, 0, 0, 0, 0⟩

/-- A selected native table slot. Canonical padding on a carried halt takes
choice zero and malformed choices have no successful slot. -/
def pick (p : Program) (old : Code p.extra M) (bit : Bool) : Option (Instruction p.extra) :=
  match old with
  | .accepted => if bit then none else some (carry _)
  | .rejected => none
  | .running c _ => chosenInstruction (row p c) bit

/-- The native call consumes a branch bit exactly on a two-slot running row. -/
def branchBits (p : Program) (s : Code p.extra M) (bit : Bool) : List Bool :=
  match s with
  | .running c _ => LiveEvaluatorRAMDispatch.dispatchBits (row p c) bit
  | .accepted | .rejected => []

/-- Accepted slots with identical native bit strings have the same padded
witness bit. This also covers the zero-bit native accepting carry. -/
theorem pick_bit_unique (p : Program) (s : Code p.extra M) {b b' : Bool} {a a' : Instruction p.extra}
    (h : pick p s b = some a) (h' : pick p s b' = some a')
    (hb : branchBits p s b = branchBits p s b') : b = b' := by
  cases s with
  | rejected => contradiction
  | accepted => cases b <;> cases b' <;> simp_all [pick]
  | running c hc =>
    cases he : row p c <;> cases b <;> cases b' <;>
      simp_all [pick, branchBits, chosenInstruction, LiveEvaluatorRAMDispatch.dispatchBits]

/-- The first tape's finite cell window extracted from an encoded evaluator configuration. -/
def first (s : Code extra M) : TapeWindow M := ⟨s.firstCell⟩
/-- The second tape's finite cell window extracted from an encoded evaluator configuration. -/
def second (s : Code extra M) : TapeWindow M := ⟨s.secondCell⟩

/-- At an accepting target the comparison scans the zero tape fields. At a
continuing target it scans the shift, write and clipped endpoints. -/
def tapeCheck (halt : Bool) (old out : TapeWindow M) (write move : Symbol) : Prop :=
  if halt then ∀ i, out.cells i = 0
  else boundaryBlank old write move = true ∧ out = updatedWindow old write move

/-- The successful-transition test requiring a positive matching target state and the proposed
write and motion on both tape windows. -/
def checks (old out : Code extra M) (a : Instruction extra) : Prop :=
  0 < a.target.val ∧ out.stateWord = a.target ∧
    tapeCheck (decide (a.target.val = 1)) (first old) (first out) a.firstSymbol a.firstMove ∧
    tapeCheck (decide (a.target.val = 1)) (second old) (second out) a.secondSymbol a.secondMove

private theorem stateWord_accept_iff (z : Code extra M) : z.stateWord.val = 1 ↔ z = .accepted := by
  cases z with
  | accepted | rejected => simp [Code.stateWord]
  | running c hc => simp [Code.stateWord, show c.state.val ≠ 1 by omega]

private theorem checks_carry (z : Code extra M) : checks .accepted z (carry _) ↔ z = .accepted := by
  constructor
  · intro h
    exact (stateWord_accept_iff z).mp (congrArg Fin.val h.2.1)
  · rintro rfl
    simp [checks, carry, first, second, tapeCheck, Code.stateWord, Code.firstCell, Code.secondCell]

theorem checks_advance_iff (s : ConfigWindow extra M) (hs : 2 ≤ s.state.val) (z : Code extra M)
    (a : Instruction extra) :
    checks (.running s hs) z a ↔ advanceCode s a = some z ∧ z ≠ .rejected := by
  by_cases ha : a.target.val = 1
  · have hw (v : Code extra M) : v.stateWord = a.target ↔ v = .accepted := by
      rw [Fin.ext_iff, ha, stateWord_accept_iff]
    cases z <;> simp [checks, hw, advanceCode, ha, tapeCheck, first, second, Code.firstCell, Code.secondCell]
  by_cases hr : a.target.val = 0
  · simp [checks, advanceCode, hr, eq_comm]
  have ht : 2 ≤ a.target.val := by omega
  cases z with
  | accepted =>
    have hne : (Code.accepted (extra := extra) (M := M)).stateWord ≠ a.target :=
      fun h => ha (congrArg Fin.val h.symm)
    simp [checks, advanceCode, ha, hr, hne]
  | rejected =>
    have hne : (Code.rejected (extra := extra) (M := M)).stateWord ≠ a.target :=
      fun h => hr (congrArg Fin.val h.symm)
    simp [checks, hne]
  | running z hz =>
    have hfirst (v : ConfigWindow extra M) (hv : 2 ≤ v.state.val) :
        first (.running v hv) = v.firstTape := rfl
    have hsecond (v : ConfigWindow extra M) (hv : 2 ≤ v.state.val) :
        second (.running v hv) = v.secondTape := rfl
    simp [checks, tapeCheck, ha, Code.stateWord, hfirst, hsecond, advanceCode, hr,
      show 0 < a.target.val by omega, ConfigWindow.ext_iff]
    tauto

/-- This equivalence preserves the specified choice bit, even for distinct
slots whose five published words coincide. -/
theorem pick_checks_iff (p : Program) (old out : Code p.extra M) (bit : Bool) :
    (∃ a, pick p old bit = some a ∧ checks old out a) ↔
      nextCode p old bit = some out ∧ out ≠ .rejected := by
  cases old with
  | accepted => cases bit <;> cases out <;> simp [pick, nextCode, checks_carry]
  | rejected => simp [pick, nextCode, eq_comm]
  | running s hs =>
    simp only [pick, nextCode]
    cases h : chosenInstruction (row p s) bit with
    | none => simp [eq_comm]
    | some a => simp [checks_advance_iff]

end LiveEvaluatorAction

end VPVNP
end Computability
end OAI
