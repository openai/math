import OAI.Computability.BorderVNP.CubeTeamNativeLayout
import OAI.Computability.BorderVNP.RoutingISATableClear

/-! # Native frame loading and team-total initialization -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamNative

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Read the group count and its three arrays from fields 74–77.
Field 1 is the common physical team count. -/
def loadTeamLayout : Code := .block [
  .constant 0 0, .constant 1 1, readFrame 3 62 63 1, readFrame 4 62 63 74,
  readFrame 5 62 63 75, readFrame 6 62 63 76, readFrame 7 62 63 77]

/-- Numeric contents of the group-assignment frame. -/
structure Layout.Frame (l : Layout) (frame : ℕ) (mem : ℕ → ℕ) : Prop where
  teamCount : mem (frame+1) = l.r+1
  groupCount : mem (frame+74) = l.groups
  weightBase : mem (frame+75) = l.weights
  totalBase : mem (frame+76) = l.totals
  ownerBase : mem (frame+77) = l.owners

/-- Every parameter used by the scheduler is read from its physical frame. -/
theorem run_loadTeamLayout {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout)
    (fit : readings pub 0+77 < 2^w) (h : l.Frame (readings pub 0) (readings m)) :
    BoundedRun pub macros loadTeamLayout s m loadTeamLayout.slots
      (fun z => l.Ready z ∧ z.mem = readings m) := by
  have safe (d : Reg) (f : Word 8) (z : NatState) (hf : f.val ≤ 77) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ z w (by omega)
  apply (loadTeamLayout.runFixed pub macros s m ?_).mono le_rfl
  · rintro _ rfl
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_⟩ <;>
      simp (config := {decide := true}) [loadTeamLayout,Code.block,Code.fixedEval,
        readFrame_fixedEval,Code.evalNat,NatState.ofWords,h.teamCount,h.groupCount,
        h.weightBase,h.totalBase,h.ownerBase]
  · simp (config := {decide := true}) [loadTeamLayout,Code.block,Code.fixedSafe,Code.safeReadOnly,
      safe _ _ _ (by decide : (1 : Word 8).val ≤ 77), safe _ _ _ (by decide : (74 : Word 8).val ≤ 77),
      safe _ _ _ (by decide : (75 : Word 8).val ≤ 77), safe _ _ _ (by decide : (76 : Word 8).val ≤ 77),
      safe _ _ _ (by decide : (77 : Word 8).val ≤ 77)]
    by_contra he; subst w; simp at fit

/-- Initialize all team totals before the public traversal of the group table. -/
def clearTotals : Code := .seq (.copy 9 0) (.whileLt 9 3 (.block [
  .binary .add 12 6 9, .store 12 0, .binary .add 9 9 1]))

/-- Initialization produces precisely the empty group prefix, preserving all
addresses outside the team-total array. -/
theorem run_clearTotals {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (ws : ℕ → ℕ) (al : l.Allocated w)
    (ready : l.Ready (.ofWords s m)) :
    BoundedRun pub macros clearTotals s m (4*(l.r+1)+2)
      (fun z => l.Ready z ∧ Tables l ws (readings m) 0 z.mem) := by
  let b := Code.block [.binary .add 12 6 9, .store 12 0, .binary .add 9 9 1]
  let P (i : ℕ) (z : NatState) := l.Ready z ∧ z.reg 9 = i ∧
    z.mem = zeroPrefix l.totals i (readings m)
  have regs (i : ℕ) (z : NatState) (h : P i z) : z.reg 9 = i ∧ z.reg 3 = l.r+1 :=
    ⟨h.2.1,h.1.teamCount⟩
  have step (i : ℕ) (hi : i < l.r+1) (u : Bank w) (mu : Memory w)
      (h : P i (.ofWords u mu)) : BoundedRun pub macros b u mu 3 (P (i+1)) := by
    let z := NatState.ofWords u mu
    have h0 : z.reg 0 = 0 := h.1.zeroReg
    have h1 : z.reg 1 = 1 := h.1.oneReg
    have h6 : z.reg 6 = l.totals := h.1.totalBase
    have h9 : z.reg 9 = i := h.2.1
    have hf : l.totals+i < 2^w := al.totalsFit ⟨i,hi⟩
    have inc : i+1 < 2^w := Nat.lt_of_le_of_lt hi (h.1.teamCount ▸ (u 3).isLt)
    have safe : b.fixedSafe w (readings pub) z := by
      simp (config := {decide := true}) [b,Code.block,Code.fixedSafe,Code.fixedEval,Code.evalNat,
        Code.safeReadOnly,addressOpFits,h6,h9,h1,hf,inc]
    apply (b.runFixed pub macros u mu safe).mono (by decide)
    rintro y rfl
    refine ⟨h.1.congr (fun j hj => b.fixedEval_protected _ _ (by decide) j hj),?_,?_⟩
    · change (b.fixedEval _ z).reg 9 = i+1
      simp (config := {decide := true}) [b,Code.block,Code.fixedEval,Code.evalNat,addressOp,h9,h1]
    · change (b.fixedEval _ z).mem = _
      simp (config := {decide := true}) [b,Code.block,Code.fixedEval,Code.evalNat,addressOp,h6,h9,h0]
      rw [show z.mem = _ from h.2.2,extend_zeroPrefix]
  have run := ((Code.copy 9 0).runFixed pub macros s m trivial).seq (b := .whileLt 9 3 b)
    (t := (l.r+1-0)*(3+1)+1) (Q := P (l.r+1)) (fun u mu hu =>
    run_counted_loop pub macros 9 3 b (l.r+1) 3 P regs step 0 (by omega) u mu (by
      rw [hu]
      refine ⟨ready.congr (fun j hj => Code.fixedEval_protected _ _ _ (by decide) j hj),?_,?_⟩
      · simpa [Code.fixedEval,Code.evalNat] using ready.zeroReg
      · funext a
        simp [zeroPrefix,Code.fixedEval,NatState.ofWords]))
  apply run.mono (by change 1+(l.r+1-0)*(3+1)+1 ≤ 4*(l.r+1)+2; omega)
  rintro z ⟨hz,_,hm⟩
  rw [hm]
  refine ⟨hz,⟨?_,fun i hi => False.elim (Nat.not_lt_zero i hi),?_⟩⟩
  · intro j
    simp [zeroPrefix,loads,j.isLt]
  · intro a ht _
    have hn : ¬ (l.totals ≤ a ∧ a < l.totals+(l.r+1)) := by
      rintro ⟨hlo,hhi⟩
      exact ht ⟨a-l.totals,by omega⟩ (by dsimp; omega)
    simp [zeroPrefix,hn]

end Cube.TeamNative

end BorderVNP
end Computability
end OAI
