import OAI.Computability.BorderVNP.RoutingISATableBounds
import Mathlib.Tactic.IntervalCases

/-! # Loading and validating the fixed scheduling frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Fixed-state evaluation of a public field read through scratch registers 62 and 63. -/
theorem readFrame_fixedEval (d : Reg) (f : Word 8) (pub : Arg → ℕ) (s : NatState) :
    (readFrame d 62 63 f).fixedEval pub s = ⟨Function.update
      (Function.update (Function.update s.reg 63 f.val) 62 (pub 0+f.val)) d
        (s.mem (pub 0+f.val)), s.mem⟩ := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.fixedEval, Code.evalNat, addressOp,
    Function.update_comm (show (62 : Reg) ≠ 63 by decide)]

/-- A public field read fits whenever its frame address fits. -/
theorem readFrame_fixedSafe (d : Reg) (f : Word 8) (pub : Arg → ℕ) (s : NatState)
    (w : ℕ) (hf : pub 0+f.val < 2^w) :
    (readFrame d 62 63 f).fixedSafe w pub s := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.fixedSafe, Code.fixedEval,
    Code.safeReadOnly, Code.evalNat, addressOpFits, hf]
  omega

set_option maxHeartbeats 1000000 in
/-- The setup fragment reads all configuration registers from the actual allocated frame,
rejecting small team counts. Under the layout assumptions it returns with memory intact. -/
theorem run_tableSetup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : TableLayout) (al : l.Allocated w) (hf : (pub 0).val = l.frame)
    (hmem : l.frameFields (readings m)) :
    BoundedRun pub macros tableSetup s m tableSetup.slots
      (fun z => l.ready z ∧ z.mem = readings m) := by
  obtain ⟨ht,hr,hc,hw,ho,hu,hd⟩ := hmem
  have hR := al.teamCount
  have hs : l.teams*l.teams < 2^w := by simpa only [pow_two] using al.square
  have ha : l.frame+21 ≤ 2^w := al.fits .frame
  have wn : w ≠ 0 := by rintro rfl; simp at ha
  have hf' : readings pub 0 = l.frame := hf
  have fs (d : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 20) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ _ _ (by rw [hf']; omega)
  apply (Code.runFixed tableSetup pub macros s m ?_).mono le_rfl
  · rintro _ rfl
    constructor
    · intro j hj
      rcases j with ⟨j,hj'⟩
      change j ≤ 12 at hj
      interval_cases j <;>
        simp (config := { decide := true }) [tableSetup, Code.block, readFrame_fixedEval, requireLt,
          Code.fixedEval, Code.evalNat, addressOp, NatState.ofWords, hf', ht,hr,hc,hw,ho,hu,hd,
          hR, TableLayout.regValue]
    · simp (config := { decide := true }) [tableSetup, Code.block, readFrame_fixedEval, requireLt,
        Code.fixedEval, Code.evalNat, NatState.ofWords, hf', ht, hR]
  · simp (config := { decide := true }) [tableSetup, Code.block, requireLt, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, readFrame_fixedEval, NatState.ofWords,
      hf', ht,hR,hs, fs _ _ _ (by decide : (1 : Word 8).val ≤ 20),
      fs _ _ _ (by decide : (12 : Word 8).val ≤ 20), fs _ _ _ (by decide : (13 : Word 8).val ≤ 20),
      fs _ _ _ (by decide : (16 : Word 8).val ≤ 20), fs _ _ _ (by decide : (17 : Word 8).val ≤ 20),
      fs _ _ _ (by decide : (18 : Word 8).val ≤ 20), fs _ _ _ (by decide : (20 : Word 8).val ≤ 20)]
    omega

end RoutingISA

end BorderVNP
end Computability
end OAI
