import OAI.Hierarchy.ProtocolRAMTurnActiveChart
import OAI.Hierarchy.ProtocolRAMHalfRole

namespace OAI
/-! # Reading the actual old directed sites, width, and even-tagged role ordinals -/
namespace Hierarchy.ProtocolRAMTurnChart
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM
open scoped Fin.CommRing
variable {W N : ℕ}

/-- The native memory itself supplies every input word. Authentication at a
needed typed original or paid endpoint is provided separately by its live receipt. -/
def captured (d : Data) (m : Memory W) : Words where
  rawSource j := (d.rawSource.read m (j:Word W)).val
  rawTarget j := (d.rawTarget.read m (j:Word W)).val
  width j := (d.oldWidth.read m (j:Word W)).val
  sourceRole j := (d.sourceRole.read m (j:Word W)).val
  targetRole j := (d.targetRole.read m (j:Word W)).val

theorem captured_at (d : Data) (m : Memory W) (u : Geometry) (roles : ℕ)
    (decode : ∀r, r<2*roles → d.half.read m (r:Word W)=((r/2:ℕ):Word W))
    (source : (captured d m).sourceRole u.item<2*roles) (target : (captured d m).targetRole u.item<2*roles) :
    d.At (captured d m) m u :=
  ⟨(Fin.cast_val_eq_self _).symm,(Fin.cast_val_eq_self _).symm,(Fin.cast_val_eq_self _).symm,
   (Fin.cast_val_eq_self _).symm,(Fin.cast_val_eq_self _).symm,decode _ source,decode _ target,
   Fin.isLt _,Fin.isLt _⟩

theorem captured_width (d : Data) (m : Memory W) (u : Geometry) :
    d.oldWidth.read m (u.item:Word W)=((captured d m).width u.item:Word W) := (Fin.cast_val_eq_self _).symm

theorem captured_reverse (d : Data) (m : Memory W) (u : Geometry) (source target : ℕ)
    (rawL : (d.rawSource.read m (u.item:Word W)).val=source)
    (rawR : (d.rawTarget.read m (u.item:Word W)).val=target) :
    rev (captured d m) u.item=decide (¬source<target) := by
  simp only [rev,captured,rawL,rawR]

theorem captured_role (d : Data) (m : Memory W) (u : Geometry) (s : Bool) (r : ℕ)
    (typed : (if s then d.targetRole else d.sourceRole).read m (u.item:Word W)=(r:Word W)) (small : r<2^W) :
    (if s then (captured d m).targetRole else (captured d m).sourceRole) u.item=r := by
  have read := (congrArg Fin.val typed).trans (Fin.val_cast_of_lt small)
  cases s <;> exact read

end Hierarchy.ProtocolRAMTurnChart

end OAI
