import OAI.Computability.BorderVNP.CubeScatterPaddingLayout
import OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-! # Loading the padding verifier from the genuine RAM frame and powers table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open private indirect_eval from OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-- Load all fixed bases, the exponent at the selected axis, and the number of
ordered label pairs. The caller supplies only the original shared frame address. -/
def setup : Code := .block [
  .constant 0 0, .constant 1 1, .constant 2 2, .constant 3 3,
  readFrame 4 62 63 59, readFrame 7 62 63 56, .binary .mul 5 7 7,
  readFrame 8 62 63 77, readFrame 9 62 63 57, readFrame 11 62 63 91,
  readFrame 12 62 63 88, readFrame 6 62 63 62, readFrame 27 62 63 63,
  SharedRows.indirect 34 5, .binary .add 6 6 34, .load 6 6,
  SharedRows.indirect 24 8, SharedRows.indirect 25 7,
  readFrame 26 62 63 61, readFrame 27 62 63 93, readFrame 28 62 63 94, readFrame 29 62 63 0]

/-- Actual frame, declaration and selected powers-table addresses are representable. -/
structure HeaderFits (w frame : ℕ) (mem : ℕ → ℕ) : Prop where
  frameEnd : frame+94 < 2^w
  declarationEnd : mem (frame+63)+8 < 2^w
  selectedPower : mem (frame+62)+mem (mem (frame+63)+5) < 2^w
  pairs : mem (frame+56)*mem (frame+56) < 2^w

set_option maxHeartbeats 800000 in
/-- The genuine startup instructions populate the register cache from the supplied
memory image, leaving all its words intact. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame : ℕ) (atFrame : readings pub 0=frame)
    (room : HeaderFits w frame (readings m)) :
    BoundedRun pub macros setup s m setup.slots (fun z =>
      (Layout.fromFrame frame (readings m)).Ready z ∧ z.mem=readings m) := by
  obtain ⟨endFrame,header,power,pairs⟩ := room
  have fs (d : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 94) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ z w (by rw [atFrame]; omega)
  have hw : w ≠ 0 := by rintro rfl; norm_num at endFrame
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,
      Code.evalNat,readFrame_fixedEval,SharedRows.indirect,NatState.ofWords,atFrame,addressOpFits,addressOp,hw,fs]
    omega
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  simp (config := {decide := true}) [Layout.Ready,Layout.fromFrame,Layout.count,setup,Code.block,Code.fixedEval,
    Code.evalNat,readFrame_fixedEval,indirect_eval,NatState.ofWords,atFrame,addressOp]

end Cube.Padding

end BorderVNP
end Computability
end OAI
