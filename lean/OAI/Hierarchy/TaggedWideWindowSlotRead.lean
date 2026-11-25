import OAI.Hierarchy.TaggedWidePublishedSlots

namespace OAI
/-! # Keeping the two scaled socket operands through the terminal write -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {W T H : ℕ} (p : Dated T) (work : ℕ)

/-- Only the occupied part of either socket bank is read. Every such word is
strictly below the first native terminal destination, even if the padded bank is longer. -/
theorem Dated.slot_read_below (work : ℕ) (m out : Memory W)
    (keep : ∀a,a<p.workEnd work→ out a=m a) (room : p.workEnd work<2^W)
    (side : Bool) (j : Fin p.rawEdges) :
    (p.slotBank work side).read out (j.val:Word W)=(p.slotBank work side).read m (j.val:Word W) := by
  have inside : ∀b, p.slotBase work b+j.val<p.workEnd work := by
    intro b
    have := j.isLt
    cases b <;> simp only [Dated.slotBase,Dated.workEnd,Bool.toNat_false,Bool.toNat_true,
      zero_mul,one_mul] <;> omega
  have fit : j.val<2^W := by have:=inside side;omega
  have cap : p.rawEdges≤(p.slotBank work side).size := (ProtocolRAMPurchaseSampler.lt_span _).le
  change out (p.slotBase work side+(j.val:Word W).val%(p.slotBank work side).size)=
    m (p.slotBase work side+(j.val:Word W).val%(p.slotBank work side).size)
  rw [Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt (j.isLt.trans_le cap)]
  exact keep _ (inside side)

/-- Both native scans use the original memory for their socket expressions.
The result applies at any subsequent output preserving the dated allocation. -/
theorem slot_pair_ports (m : Memory W) (fits : ∀b,(p.orderedSlot b).Fits W (p.slotStart work))
    (room : p.workEnd work<2^W) {J : Type*} (row : J→Fin p.rawEdges)
    (port : Bool→J→Fin H)
    (operand : ∀j side,(p.orderedSlot side).eval m ((row j).val:Word W)=((port side j).val:Word W)) :
    ∃out,(((p.slotPage work false).code W).seq ((p.slotPage work true).code W)).Exec m out
      ((p.slotPage work false).ticks+(p.slotPage work true).ticks) ∧
      (∀a,a<p.slotStart work→ out a=m a) ∧ ∀later : Memory W,
      (∀a,a<p.workEnd work→later a=out a) → ∀side j,
        (p.slotBank work side).read later ((row j).val:Word W)=((port side j).val*p.lanes:ℕ) := by
  obtain ⟨out,exec,both,frame⟩:=slot_pair_run p work m fits room
  refine ⟨out,exec,frame,?_⟩
  intro later keep side j
  rw [p.slot_read_below work out later keep room,both,operand]
  push_cast
  ring

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
