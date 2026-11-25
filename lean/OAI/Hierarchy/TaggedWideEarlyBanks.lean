import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Rounded chronological role and ballot banks fit before the first native control write -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles RoleProgram
open scoped Classical BigOperators
variable {T : ℕ} (g : Dated T)
local notation "S" => stride (fun i=>(g.ballot i).span g.sites)

private theorem span_before (j : Fin T) : 1+g.sites*(g.ballot j).columns≤S := by
  have h : (g.ballot j).span g.sites≤S :=
    Finset.single_le_sum (s:=Finset.univ) (fun i _=>Nat.zero_le ((g.ballot i).span g.sites)) (Finset.mem_univ j)
  exact (Nat.le_add_right ..).trans h

theorem Dated.role_bank_before_control (work later : ℕ) (near : work≤later)
    (j : Fin T) (date : Fin (T+1)) (f : Fin 3) (enough : g.roleWords+2≤T*S) :
    let b:=DatedRoleSheets.bank g.physical (g.roleStart work date) g.roleWords
      (ProtocolRAMPurchaseSampler.bits g.roleWords) f
    b.base+b.size≤g.controlBase later j+1 := by
  intro b
  have hf:=Nat.mul_le_mul_right g.roleSpan (show f.val+1≤3 by omega)
  have dt:=Nat.mul_le_mul_right (3*g.roleSpan) (show date.val+1≤T+1 by omega)
  rw [Nat.succ_mul] at hf dt
  have s : 1+g.roleWords≤g.roleSpan:=Nat.le_add_right ..
  have binary:=ProtocolRAMPurchaseSampler.span_le g.roleWords
  change work+date.val*(3*g.roleSpan)+f.val*g.roleSpan+1+ProtocolRAMPurchaseSampler.span g.roleWords≤
    later+(T+1)*(3*g.roleSpan)+T*S+j.val*stride (fun i=>(g.control i).span g.sites)+1
  omega

theorem Dated.ballot_bank_before_control (work : ℕ) (j : Fin T) (reserve : j.val+2≤T) :
    let b:=RoleROM.bank (g.ballotStart work j+1) (g.sites*(g.ballot j).columns)
    b.base+b.size≤g.controlBase work j+1 := by
  intro b
  have before:=Nat.mul_le_mul_right S reserve
  rw [Nat.add_mul] at before
  have one:=span_before g j
  have binary:=ProtocolRAMPurchaseSampler.span_le (g.sites*(g.ballot j).columns)
  change g.rolesEnd work+j.val*S+1+ProtocolRAMPurchaseSampler.span (g.sites*(g.ballot j).columns)≤
    g.rolesEnd work+T*S+j.val*stride (fun i=>(g.control i).span g.sites)+1
  omega

theorem Dated.ballot_clearance (live : Fin T) (width : g.roleCount≤(g.ballot live).columns) (dates : 2≤T) :
    g.roleWords+2≤T*S := by
  have cost:=span_before g live
  have cap:=Nat.mul_le_mul_left g.sites width
  have reserve:=Nat.mul_le_mul_right S dates
  change g.sites*g.roleCount+2≤_
  omega

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
