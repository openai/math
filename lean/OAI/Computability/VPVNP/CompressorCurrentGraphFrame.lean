import OAI.Computability.VPVNP.CompressorCurrentGraph

/-! # Retaining the original cursor frame at all selected boundaries -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CurrentGraph

open BurstRAM Compression DescriptorSpace BlockHeaderRun SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {L : Layout} {m out : Memory w}

/-- The eight persistent input words begin at level zero, scalar offset six. -/
def frameCell (L : Layout) (x : ℕ) := levelStart L 0+6 ≤ x ∧ x < levelStart L 0+14

theorem frame_keep (room : levelStart L 0+13 < 2^w) (same : ∀ x, frameCell L x → out x=m x) :
    (Frame.data (header w L 0+6) out : Fin 8 → Word w)=Frame.data (header w L 0+6) m := by
  funext j
  change out (header w L 0+6+(j.val : Word w)).val = m (header w L 0+6+(j.val : Word w)).val
  apply same
  have addr : (header w L 0+6+(j.val : Word w)).val=levelStart L 0+(6+j.val) := by
    rw [show header w L 0+6+(j.val : Word w)=((levelStart L 0+(6+j.val) : ℕ) : Word w) by
      simp [header,add_assoc]]
    exact Nat.mod_eq_of_lt (by have := j.isLt; omega)
  rw [addr]
  unfold frameCell
  have := j.isLt; omega

theorem frame_transfer (room : levelStart L 0+13 < 2^w) (agree : Agree (levelStart L 0 ≤ ·) m out) :
    (Frame.data (header w L 0+6) out : Fin 8 → Word w)=Frame.data (header w L 0+6) m :=
  frame_keep room (fun x hx => (agree x ((Nat.le_add_right ..).trans hx.1)).symm)

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → R} {hf : B.IsSolution f}

theorem frame_publish (v : SelectedLevel B f hf) {old new : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    (run : Substep v L old new six m) (next : old.val+1=new.val)
    (fields : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) :
    (Frame.data (header w L 0+6) (finalMemory v L old new m) : Fin 8 → Word w)=Frame.data (header w L 0+6) m :=
  run.cursorFrame v next fields fit

end CompressorRecords.CurrentGraph

end VPVNP
end Computability
end OAI
