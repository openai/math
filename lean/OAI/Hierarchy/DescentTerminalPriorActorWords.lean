import OAI.Hierarchy.DescentTerminalPreflightPriorRun

namespace OAI
/-! # Reading the actor bitmap at the end of population and actor repacking -/
namespace Hierarchy.DescentTerminalPriorArena
open DescentSIMDLookup DescentTerminalPrimitiveArena ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) (groups mPaid mAct paidBits extBits origin : ℕ)
local notation "p0" => pop s groups mPaid paidBits extBits origin
local notation "act" => actStart s groups mPaid paidBits extBits origin
local notation "a0" => actor s groups mPaid mAct paidBits extBits 1 origin
local notation "stop" => start s groups mPaid mAct paidBits extBits 1 origin
variable {w : ℕ} (paid src : Fin s.blocks → Bank) (ext : Bank) (nodeBits : ℕ)
local notation "pick" => (fun (_ : Fin s.blocks) (u : Cell 1) => u)
local notation "out_" => final (s:=s) (groups:=groups) (mPaid:=mPaid) (mAct:=mAct)
  (paidBits:=paidBits) (extBits:=extBits) (actBits:=1) (origin:=origin)
  (paid:=paid) (actorSrc:=src) (ext:=ext) (nodeBits:=nodeBits) («pick»:=pick)

/-- The actor bitmap depends only on the old actor rows, even though the
population words are computed first. -/
theorem repacked_actor (m : Memory w) (early : Earlier s groups mPaid mAct origin paid src ext)
    (room : stop < 2^w) (positive : 0 < mAct) (bits : Fin s.blocks → Fin s.shops → Fin groups → Cell 1)
    (rows : ∀ b, ∀ j : Row s.shops groups mAct,
      m ((src b).base + (row s.shops groups mAct j).val) = ((data (bits b) j).val : Word w)) :
    ∀ b (h : Fin s.shops), out_ m ((s.subrow a0 b).base + h.val) =
      ((encode 1 groups (bits b h)).val : Word w) := by
  have popRoom : p0 + s.rows < 2^w := by unfold start actor actStart at room; omega
  have startLe : origin ≤ act := by unfold actStart pop; omega
  have actRoom : a0 + s.rows < 2^w := by unfold start at room; omega
  have actStartRoom : act < 2^w := by unfold actor at actRoom; omega
  have fit := paid_fit s groups mPaid mAct paidBits extBits 1 origin paid src ext early room
  let mid := DescentTerminalPopulation.RAM.done s.shops groups mPaid paidBits nodeBits extBits origin paid ext m
  have mounted := DescentTerminalPopulation.RAM.run s.shops groups mPaid paidBits nodeBits extBits origin
    paid ext m fit popRoom
  have sourceFit (b) : (src b).Fits w act := by
    have low := (early.acEnd b).trans startLe
    exact ⟨Nat.two_pow_pos _, (Nat.le_add_left ..).trans_lt (low.trans_lt actStartRoom), low⟩
  have kept (b) (j : Row s.shops groups mAct) :
      mid ((src b).base + (row s.shops groups mAct j).val) = ((data (bits b) j).val : Word w) := by
    have idx := (row s.shops groups mAct j).isLt.trans_le (early.acSize b)
    have before := early.acEnd b
    exact (mounted.2.2 _ (.inl (by omega))).trans (rows b j)
  exact (DescentTerminalActorRepack.issued pick s.shops groups mAct act src mid sourceFit
    early.acSize actRoom (fun _ => rfl) positive bits kept).2.2.1

end
end Hierarchy.DescentTerminalPriorArena

end OAI
