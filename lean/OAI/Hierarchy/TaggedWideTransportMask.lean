import OAI.Hierarchy.TaggedWideStageWidthRun
import OAI.Hierarchy.TaggedWidePrivateOrdinals

namespace OAI
/-! # The actual shared width table for the positive-scale compactors -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ProbeStage CoreBoard HistoryRoles RoleROM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open Tagged.WideStack ProtocolRAMEmit
open scoped Classical Fin.CommRing

variable {W T : ℕ} (p : Dated T) (rom work : ℕ)
local notation "z" => p.widthPage rom work
local notation "N" => p.rawEdges
local notation "base" => (p.stageWidth work).base

def transportWords (positive : Fin N → Prop) (i : Fin N) : ℕ := (decide (positive i)).toNat

theorem triple_eval (m : Memory W) (i : Fin N) :
    triple.eval m (i.val:Word W)=((3*i.val:ℕ):Word W) := by
  simp only [triple,Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem measured_width (dst : ℕ) (rows : Fin N → Row) (m old : Memory W)
    (origin : p.measured.base=dst+3*N+1) (within : 3*N≤p.measured.size) (fit : 3*N≤2^W)
    (frame : ∀a,dst≤a → a<dst+9*N → m a=emitted dst rows old a) (i : Fin N) :
    p.measured.read m ((3*i.val:ℕ):Word W)=((rows i).width:Word W) := by
  have low : 3*i.val<3*N := by have:=i.isLt;omega
  change m (p.measured.base+((3*i.val:ℕ):Word W).val%p.measured.size)=_
  rw [Fin.val_cast_of_lt (low.trans_le fit),Nat.mod_eq_of_lt (low.trans_le within),origin]
  rw [show dst+3*N+1+3*i.val=dst+3*N+3*i.val+1 by omega,frame _ (by omega) (by omega)]
  exact (emitted_read dst rows old i 1).2.1

/-- A zero-filled three-word row for each original edge keeps the stride used by all
the fixed-width classification and candidate compaction programs. -/
theorem width_run (positive : Fin N → Prop) (rows : Fin N → Row) (m : Memory W)
    (mounted : RoleROM.Mounted (p.maskROM rom) (transportWords p positive) m)
    (native : ∀i : Fin N,p.measured.read m ((3*i.val:ℕ):Word W)=((rows i).width:Word W))
    (vf : (z).value.Fits W base)
    (room : p.slotStart work<2^W) :
    ∃out,((z).code W).Exec m out (z).ticks ∧
      (∀i : Fin N,(p.stageWidth work).read out ((3*i.val:ℕ):Word W)=
        ((atScale positive (fun _=>0) 0 rows i).width:Word W)) ∧
      ∀a,a<p.maskStart work → out a=m a := by
  let live (i : Fin N) := decide (positive i)
  have bound : N ≤ 2^W := by
    unfold Dated.slotStart at room
    omega
  have one : 1 < 2^W := by
    unfold Dated.slotStart at room
    omega
  have origins (i : Fin N) :
      (RoleROM.bank (p.maskROM rom) N).read m (i.val : Word W) = (live i).toNat :=
    RoleROM.read mounted .row (i.val : Word W) i bound rfl
  obtain ⟨out, ran, read, frame⟩ := width_run_flags p rom work m live (fun i => (rows i).width)
    origins native vf.2.2.2.1 vf.1.1 room one
  refine ⟨out, ran, ?_, fun a ha => frame a (Or.inl ha)⟩
  intro i
  by_cases hot : positive i <;> simpa [atScale, live, hot] using read i

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
