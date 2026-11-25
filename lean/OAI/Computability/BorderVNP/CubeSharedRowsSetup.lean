import OAI.Computability.BorderVNP.CubeSharedRowsPass

/-! # Reading the real group, declaration and bank frames before shared-row emission -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The actual public layout produced by the data, declaration and group-assignment passes. -/
structure Layout.Fields (l : Layout) (mem : ℕ → ℕ) : Prop where
  /-- Record buffer and the number of already written data rows. -/
  records : mem (l.frame+12) = l.records ∧ mem (l.frame+13) = l.dataCount
  /-- Alphabet size and cube dimension. -/
  shape : mem (l.frame+59) = l.groups ∧ mem (l.frame+60) = l.axes
  /-- Declaration header pointer. -/
  declaration : mem (l.frame+63) = l.header
  /-- The public base of the owner map. -/
  owners : mem (l.frame+77) = l.owners
  /-- Ordered pair-bank base and address stride. -/
  views : mem (l.frame+85) = l.banks ∧ mem (l.frame+86) = l.stride
  /-- Crossing-width matrix, chosen coordinate and fixed selector length. -/
  header : mem (l.header+1) = l.lengths ∧ mem (l.header+5) = l.axis ∧ mem (l.header+6) = l.selectors

/-- Indirect lookup inside the declaration header, whose base is in register 27. -/
def indirect (dst : Reg) (field : Word 8) : Code :=
  .block [.constant 63 field,.binary .add 62 27 63,.load dst 62]

private theorem indirect_eval (dst : Reg) (f : Word 8) (pub : Arg → ℕ) (z : NatState) :
    (indirect dst f).fixedEval pub z =
      ⟨Function.update (Function.update (Function.update z.reg 63 f.val) 62 (z.reg 27+f.val))
        dst (z.mem (z.reg 27+f.val)),z.mem⟩ := by
  simp (config := {decide := true}) [indirect,Code.block,Code.fixedEval,Code.evalNat,addressOp]

/-- Load all twelve physical input registers, reading the variable declaration fields indirectly. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 7,
  readFrame 3 62 63 59,readFrame 4 62 63 60,readFrame 27 62 63 63,
  readFrame 6 62 63 77,readFrame 9 62 63 85,readFrame 10 62 63 86,
  readFrame 11 62 63 12,readFrame 12 62 63 13,indirect 5 5,indirect 7 1,indirect 8 6]

set_option maxHeartbeats 2000000 in
/-- The native setup obtains its actual declarations from RAM. Its cost is fixed and it leaves all memory intact. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (hf : (pub 0).val = l.frame) (h : l.Fields (readings m)) :
    BoundedRun pub macros setup s m setup.slots (fun z => l.Ready z ∧ z.mem = readings m) := by
  have hp : readings pub 0 = l.frame := hf
  have fs (d : Reg) (f : Word 8) (z : NatState) (hh : f.val ≤ 86) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ z w (by rw [hp]; have := fit.headers.1; omega)
  have room : 7 < 2^w := by have := fit.headers.1; omega
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,readFrame_fixedEval,NatState.ofWords,hp,h.declaration,room,
      fs _ _ _ (by decide : (59 : Word 8).val ≤ 86),fs _ _ _ (by decide : (60 : Word 8).val ≤ 86),
      fs _ _ _ (by decide : (63 : Word 8).val ≤ 86),fs _ _ _ (by decide : (77 : Word 8).val ≤ 86),
      fs _ _ _ (by decide : (85 : Word 8).val ≤ 86),fs _ _ _ (by decide : (86 : Word 8).val ≤ 86),
      fs _ _ _ (by decide : (12 : Word 8).val ≤ 86),fs _ _ _ (by decide : (13 : Word 8).val ≤ 86),
      indirect, addressOpFits,addressOp]
    have := fit.headers.2
    have hn : w ≠ 0 := by rintro rfl; norm_num at room
    omega
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro z rfl
  constructor
  · intro j hj
    rcases j with ⟨j,hj'⟩
    change j ≤ 12 at hj
    interval_cases j <;> simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,
      readFrame_fixedEval,indirect_eval,NatState.ofWords,hp,h.declaration,h.records.1,h.records.2,
      h.owners,h.views.1,h.views.2,h.shape.1,h.shape.2,h.header.1,h.header.2.1,h.header.2.2,Layout.regValue]
  · simp [setup,Code.block,Code.fixedEval,readFrame_fixedEval,indirect_eval,NatState.ofWords]

end Cube.SharedRows

end BorderVNP
end Computability
end OAI
