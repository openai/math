import OAI.Hierarchy.TaggedWireRoleProgramCore
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Ordered old and new role tables from the native four-column passes -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

structure Board where
  base : ℕ
  old : ℕ
  edges : ℕ
  chart : Chart
  before : Bool→Socket
  finish : Bool→Socket

namespace Board
variable (b : Board) {w : ℕ}

def newBase := b.base+4*b.old
def endAt := b.newBase+4*b.edges

def oldSite (right : Bool) := RoleROM.bank (b.base+right.toNat*b.old) b.old
def oldRole (right : Bool) := RoleROM.bank (b.base+(2+right.toNat)*b.old) b.old
def newSite (right : Bool) := RoleROM.bank (b.newBase+right.toNat*b.edges) b.edges
def newRole (right : Bool) := RoleROM.bank (b.newBase+(2+right.toNat)*b.edges) b.edges

def code (w : ℕ) := (native w b.base b.old b.chart b.before false).seq (native w b.newBase b.edges b.chart b.finish true)
def time := ticks b.base b.old b.chart b.before false+ticks b.newBase b.edges b.chart b.finish true
def final (m : Memory w) := state b.newBase b.edges b.chart b.finish true (state b.base b.old b.chart b.before false m)

theorem cheapCode : CheapCode (b.code w) :=
  cheap_seq (A:=native w b.base b.old b.chart b.before false)
    (B:=native w b.newBase b.edges b.chart b.finish true)
    (cheap (w:=w) b.base b.old b.chart b.before false)
    (cheap (w:=w) b.newBase b.edges b.chart b.finish true)

theorem time_bound : b.time≤8+4*(4+b.old*(2*volume b.chart b.before false+4))+
    4*(4+b.edges*(2*volume b.chart b.finish true+4)) := by
  have l:=tick_bound b.base b.old b.chart b.before false
  have r:=tick_bound b.newBase b.edges b.chart b.finish true
  unfold time
  omega

structure Ready (w : ℕ) : Prop where
  before : ∀j,(field b.chart b.before false j).Fits w b.base
  finish : ∀j,(field b.chart b.finish true j).Fits w b.base
  room : b.endAt<2^w

theorem output (m : Memory w) (ready : b.Ready w) :
    (b.code w).Exec m (b.final m) b.time ∧
    (∀j : Fin 4,∀i : Fin b.old,b.final m (b.base+j.val*b.old+i.val)=(field b.chart b.before false j).eval m (i.val:Word w)) ∧
    (∀j : Fin 4,∀i : Fin b.edges,b.final m (b.newBase+j.val*b.edges+i.val)=(field b.chart b.finish true j).eval m (i.val:Word w)) ∧
    (∀a,a<b.base ∨ b.endAt≤a→b.final m a=m a) := by
  have room:=ready.room
  unfold endAt newBase at room
  have lower : b.base≤b.newBase := by simp [newBase]
  let x:=state b.base b.old b.chart b.before false m
  have o:=run b.base b.old b.chart b.before false m ready.before (by omega)
  have n:=run b.newBase b.edges b.chart b.finish true x (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ lower (ready.finish j)) ready.room
  refine ⟨Procedure.Exec.then o.1 n.1,?_,?_,?_⟩
  · intro j i
    have lt : b.base+j.val*b.old+i.val<b.newBase := by
      have hi:=i.isLt
      have bound:=Nat.mul_le_mul_right b.old j.isLt
      rw [Nat.succ_mul] at bound
      unfold newBase
      omega
    exact (n.2.2 _ (.inl lt)).trans (o.2.1 j i)
  · intro j i
    exact (n.2.1 j i).trans (ProtocolRAM.eval_below (field b.chart b.finish true j) _ m x (ready.finish j)
      (fun a ha=>o.2.2 a (.inl ha)))
  · intro a outside
    rcases outside with low|high
    · exact (n.2.2 a (.inl (low.trans_le lower))).trans (o.2.2 a (.inl low))
    · exact (n.2.2 a (.inr high)).trans (o.2.2 a (.inr (by unfold endAt newBase at high;omega)))

end Board
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
