import OAI.Computability.BorderVNP.FragmentBucketLayout
import OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-! # Loading the true fragment table bases from the extended evaluator controller -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open private indirect_eval from OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-- The dynamic occupied row count is read after the sparse fragment emitter. The
other five words are the bases and cell count published by geometry. -/
structure Layout.Header (l : Layout) (frame ctl : ℕ) (mem : ℕ → ℕ) : Prop where
  pointer : mem (frame+92) = ctl
  quads : mem (ctl+28) = l.quads
  rows : mem (ctl+29) = l.rows
  cells : mem (ctl+30) = l.cells
  pairs : mem (ctl+31) = l.pairs
  triples : mem (ctl+32) = l.triples
  cursors : mem (ctl+33) = l.cursors

/-- Dereference the actual frame and controller using native public-operand and
word-load instructions. No input register contents are required. -/
def setup : Code := .block [readFrame 27 62 63 92,Cube.SharedRows.indirect 2 28,Cube.SharedRows.indirect 3 29,
  Cube.SharedRows.indirect 4 30,Cube.SharedRows.indirect 5 31,Cube.SharedRows.indirect 6 32,Cube.SharedRows.indirect 7 33]

theorem setup_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (frame ctl : ℕ) (addr : readings pub 0 = frame)
    (header : l.Header frame ctl (readings m)) (fr : frame+92 < 2^w) (cr : ctl+33 < 2^w) :
    BoundedRun pub macros setup s m setup.slots (fun z => l.Ready z ∧ z.reg 0 = (s 0).val ∧ z.mem = readings m) := by
  obtain ⟨ptr,q,n,c,b,t,u⟩ := header
  have fs := readFrame_fixedSafe 27 92 (readings pub) (.ofWords s m) w (by rw [addr]; exact fr)
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,Cube.SharedRows.indirect,readFrame_fixedEval,NatState.ofWords,addr,ptr,addressOp,addressOpFits]
    exact ⟨fs,by omega⟩
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,readFrame_fixedEval,indirect_eval,
    NatState.ofWords,Layout.Ready,addr,ptr,q,n,c,b,t,u]
  rfl

end FragmentBucket

end BorderVNP
end Computability
end OAI
