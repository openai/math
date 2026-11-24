import OAI.Computability.VPVNP.LiveEvaluatorAction
import OAI.Computability.VPVNP.LiveEvaluatorRAMScheduleData

/-!
# Semantics of all noninitial calls of one live evaluator group

The persistent cursor visits the old cells in each of the two tapes.
The comparison instruction has no nondeterministic choices. On memory
containing the published action, the complete scan verifies the two
tape conditions of that action, including the blank fields of a halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorGroup

open BurstRAM (Word Memory)
open UniversalMachine (Program Instruction Symbol)
open PrimedInputRAM (Flow)
open LiveEvaluatorEncoding (Code TapeWindow)
open LiveEvaluatorRAM (ConfigAt ActionAt TapeCellData)
open LiveEvaluatorRAM.Schedule
open LiveEvaluatorAction (tapeCheck checks first second pick)
open scoped Fin.CommRing

variable {M w : ℕ}

/-- Every noninitial call starts with fresh private registers and checks its
unique cell at the public one-based cursor. -/
def AllCells (M : ℕ) (p : Program) (pub : Pub → Word w) (m : Memory w) : Prop :=
  ∀ (side : Bool) (i : Fin (2 * M + 1)), ∃ es regs mem,
    Flow.Exec pub (cellCursor side i : Word w) (body (LiveEvaluatorRAMPrepare.prepare p))
      (fun _ => 0) m es regs mem

private theorem halt_eq {e : ℕ} (z : Code e M) (hz : z.stateWord.val = 1) : z = .accepted := by
  cases z with
  | accepted => rfl
  | rejected => contradiction
  | running c hc =>
    change c.state.val = 1 at hz
    omega

private theorem source_ne_accept (p : Program) (s : Code p.extra M) (bit : Bool) (a : Instruction p.extra)
    (h : pick p s bit = some a) (ha : a.target.val ≠ 1) : s.stateWord.val ≠ 1 := by
  intro hs
  have he := halt_eq s hs
  subst s
  cases bit
  · change some (LiveEvaluatorAction.carry p.extra) = some a at h
    exact ha (congrArg (fun r => r.target.val) (Option.some.inj h).symm)
  · contradiction

private theorem cellCursor_ne_zero (side : Bool) (i : Fin (2 * M + 1)) (hc : calls M < 2 ^ w) :
    (cellCursor side i : Word w) ≠ 0 := by
  have hlt := (cellCursor_lt_calls side i).trans hc
  intro hz
  have he := congrArg Fin.val hz
  rw [Fin.val_natCast, Nat.mod_eq_of_lt hlt, Fin.val_zero] at he
  simp [cellCursor] at he

private theorem tapeVisits_iff (p : Program) (pub : Pub → Word w) (m : Memory w)
    (old out : Code p.extra M) (a : Instruction p.extra) (side : Bool)
    (hw : 2 ≤ w) (hM : (pub 0).val = M) (hc : calls M < 2 ^ w)
    (ho : ConfigAt m (pub 1) old) (hn : ConfigAt m (pub 2) out)
    (hs : ActionAt m (pub 3) a.target.val a.firstSymbol a.firstMove a.secondSymbol a.secondMove)
    (he : a.target = out.stateWord) (hsrc : a.target.val ≠ 1 → old.stateWord.val ≠ 1) :
    (∀ i : Fin (2 * M + 1), ∃ es regs mem,
      Flow.Exec pub (cellCursor side i : Word w) (body (LiveEvaluatorRAMPrepare.prepare p))
        (fun _ => 0) m es regs mem) ↔
      tapeCheck (decide (a.target.val = 1)) (window old side) (window out side)
        (if side then a.secondSymbol else a.firstSymbol) (if side then a.secondMove else a.firstMove) := by
  have hact : ActionAt m (pub 3) out.stateWord.val a.firstSymbol a.firstMove a.secondSymbol a.secondMove :=
    he ▸ hs
  have data := fun i => scheduled_tape_data pub (fun _ => 0) m old out a.firstSymbol a.firstMove
    a.secondSymbol a.secondMove side i hw hM hc ho hn hact
  simp_rw [noninitial_call_iff p pub (cellCursor_ne_zero side _ hc)]
  change (∀ i, LiveEvaluatorRAM.cellTest (bank pub (fun _ => 0) m side i) m) ↔ _
  by_cases ha : a.target.val = 1
  · have hout : out = .accepted := halt_eq _ (he ▸ ha)
    subst out
    have hblank (i : Fin (2 * M + 1)) : (window (Code.accepted (extra := p.extra)) side).cells i = 0 := by cases side <;> rfl
    simp only [tapeCheck, ha, decide_true, ite_true, hblank, forall_const, iff_true]
    intro i
    let r := bank pub (fun _ => 0) m side i
    obtain ⟨hr, h₅, h₁₆⟩ := data i
    have h₅' : r 5 = r 1 := Fin.ext (h₅.trans hr.one.symm)
    have hnew := hr.outCell _ i hr.index
    rw [LiveEvaluatorRAM.cellTest, ite_eq_left h₅']
    constructor
    · split
      next hh =>
        have h₁ : old.stateWord.val = 1 := h₁₆.symm.trans ((congrArg Fin.val hh).trans hr.one)
        have ho' := halt_eq _ h₁
        apply Fin.ext
        rw [hr.oldCell, hr.zero, ho']
        cases side <;> rfl
      next =>
        change (m _).val < (r 3).val
        rw [hr.oldCell, hr.three]
        exact ((window old side).cells i).isLt
    · apply Fin.ext
      rw [hnew, hr.zero]
      cases side <;> rfl
  · simp only [tapeCheck, decide_eq_false ha, Bool.false_eq_true, ite_false]
    rw [← LiveEvaluatorStep.cellChecks_iff]
    apply forall_congr'
    intro i
    obtain ⟨hr, h₅, h₁₆⟩ := data i
    apply LiveEvaluatorRAM.cellTest_running_iff hr
    · exact fun heq => hsrc ha (h₁₆.symm.trans ((congrArg Fin.val heq).trans hr.one))
    · exact fun heq => ha ((congrArg Fin.val he).trans (h₅.symm.trans ((congrArg Fin.val heq).trans hr.one)))

/-- For a selected nonrejecting instruction with matching target, the two
sweeps perform exactly the checks on that instruction in the semantic code. -/
theorem allCells_iff (p : Program) (pub : Pub → Word w) (m : Memory w)
    (old out : Code p.extra M) (a : Instruction p.extra) (bit : Bool)
    (hw : 2 ≤ w) (hM : (pub 0).val = M) (hc : calls M < 2 ^ w)
    (ho : ConfigAt m (pub 1) old) (hn : ConfigAt m (pub 2) out)
    (hs : ActionAt m (pub 3) a.target.val a.firstSymbol a.firstMove a.secondSymbol a.secondMove)
    (hslot : pick p old bit = some a) (hpos : 0 < a.target.val) (he : a.target = out.stateWord) :
    AllCells M p pub m ↔ checks old out a := by
  unfold AllCells
  rw [Bool.forall_bool, tapeVisits_iff p pub m old out a false hw hM hc ho hn hs he (source_ne_accept p old bit a hslot),
    tapeVisits_iff p pub m old out a true hw hM hc ho hn hs he (source_ne_accept p old bit a hslot)]
  simp only [checks, hpos, he.symm, true_and, window, first, second, Bool.false_eq_true, ite_false, ite_true]

end LiveEvaluatorGroup

end VPVNP
end Computability
end OAI
