import OAI.Computability.BorderVNP.CubeHostScatterLayout
import OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-! # Loading the cell-cable scatter from the executing team's shared frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open private indirect_eval from OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-- Input words read by the scatter. The last two fields are reached through the
pointer in frame word 63. Word zero identifies the team in the routing ABI. -/
structure Layout.Frame (l : Layout) (mem : ℕ → ℕ) : Prop where
  /-- Team that executes the scatter. -/
  team : mem l.frame = l.team
  /-- Public cable directory and row count. -/
  cables : mem (l.frame+6) = l.cables ∧ mem (l.frame+7) = l.count
  /-- Cell labels, alphabet size and within-bin ordinals. -/
  labels : mem (l.frame+48) = l.labels ∧ mem (l.frame+56) = l.alphabet ∧ mem (l.frame+58) = l.ordinals
  /-- Owner and bank directory, and relative bit offsets. -/
  cells : mem (l.frame+72) = l.cells ∧ mem (l.frame+87) = l.relative
  /-- Pair metadata and singleton bank. -/
  pairs : mem (l.frame+91) = l.pairs ∧ mem (l.frame+88) = l.singles
  /-- Per-block width, packet-bank stride and selector prefix width. -/
  widths : mem (l.frame+61) = l.bc ∧ mem (l.frame+93) = l.bankWidth ∧ mem (l.frame+94) = l.selectorWidth
  /-- Packet bit-bank base and block count in the declaration header. -/
  declaration : mem (mem (l.frame+63)+8) = l.packets ∧ mem (mem (l.frame+63)+7) = l.blocks

/-- Decode the actual shared-memory frame used by the executing team. -/
def Layout.fromFrame (frame : ℕ) (mem : ℕ → ℕ) : Layout where
  frame := frame
  cables := mem (frame+6)
  count := mem (frame+7)
  labels := mem (frame+48)
  alphabet := mem (frame+56)
  ordinals := mem (frame+58)
  cells := mem (frame+72)
  relative := mem (frame+87)
  pairs := mem (frame+91)
  singles := mem (frame+88)
  packets := mem (mem (frame+63)+8)
  blocks := mem (mem (frame+63)+7)
  bc := mem (frame+61)
  bankWidth := mem (frame+93)
  selectorWidth := mem (frame+94)
  team := mem frame

/-- The decoded layout satisfies the scatter's frame specification for any memory image. -/
theorem Layout.fromFrame_frame (frame : ℕ) (mem : ℕ → ℕ) :
    (Layout.fromFrame frame mem).Frame mem :=
  ⟨rfl,⟨rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨rfl,rfl⟩⟩

/-- Set the four arithmetic constants, load the thirteen direct frame fields and
read the two declaration fields before reusing register 27 for the bank stride. -/
def setup : Code := .block [
  .constant 0 0, .constant 1 1, .constant 2 2, .constant 3 3,
  readFrame 4 62 63 6, readFrame 5 62 63 7, readFrame 6 62 63 48,
  readFrame 7 62 63 56, readFrame 8 62 63 58, readFrame 9 62 63 72,
  readFrame 10 62 63 87, readFrame 11 62 63 91, readFrame 12 62 63 88,
  readFrame 27 62 63 63, SharedRows.indirect 24 8, SharedRows.indirect 25 7,
  readFrame 26 62 63 61, readFrame 27 62 63 93, readFrame 28 62 63 94, readFrame 29 62 63 0]

/-- The native scatter setup has constant cost. -/
theorem setup_slots : setup.slots = 66 := by decide

set_option maxHeartbeats 2000000 in
/-- From any initial register bank, obtain every persistent scatter register and
leave the entire memory image intact. Only the two header extents must fit. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (hf : readings pub 0 = l.frame)
    (fields : l.Frame (readings m)) (frameFit : l.frame+94 < 2^w)
    (headerFit : readings m (l.frame+63)+8 < 2^w) :
    BoundedRun pub macros setup s m setup.slots (fun z => l.Ready z ∧ z.mem = readings m) := by
  obtain ⟨ht,⟨hc,hn⟩,⟨hl,ha,ho⟩,⟨hb,hr⟩,⟨hp,hs⟩,⟨hbc,hbw,hsw⟩,⟨hpk,hbl⟩⟩ := fields
  have fs (d : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 94) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ z w (by rw [hf]; omega)
  have hw : w ≠ 0 := by rintro rfl; norm_num at frameFit
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup, Code.block, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly,
      Code.evalNat, readFrame_fixedEval, SharedRows.indirect, NatState.ofWords, hf, addressOpFits, addressOp,
      hw, fs]
    omega
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro z rfl
  constructor
  · intro j hj
    rcases j with ⟨j,hj'⟩
    change j ≤ 12 ∨ 24 ≤ j ∧ j ≤ 29 at hj
    rcases hj with h | ⟨h,h'⟩ <;> interval_cases j <;>
      simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,readFrame_fixedEval,
        indirect_eval,NatState.ofWords,hf,ht,hc,hn,hl,ha,ho,hb,hr,hp,hs,hbc,hbw,hsw,hpk,hbl,Layout.regValue]
  · simp [setup, Code.block, Code.fixedEval, readFrame_fixedEval, indirect_eval, NatState.ofWords]

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
