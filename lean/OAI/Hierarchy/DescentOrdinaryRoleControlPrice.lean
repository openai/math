import OAI.Hierarchy.DescentOrdinaryRoleControlRead
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Price of the two ordinary receiver controls shared by every operand page -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty.Chronology
open scoped Classical Fin.CommRing
noncomputable section

variable (L : RoleControl.Layout) (P : Ports L.walks) (old : Fin L.blocks→Bank)

theorem gather_work : (L.gather P old).work=1+61*L.donors := by
  have one (i : Fin L.donors) : (RoleCounts.expr P old L.dictionary L.hosts i).work=50:=by
    simp only [RoleCounts.expr,peerExpr,neighborID,Expr.work]
  have pass (is : List (Fin L.donors)) :
      (Gather.collect L.tables (RoleCounts.expr P old L.dictionary L.hosts) is).work=1+61*is.length:=by
    induction is with
    | nil => rfl
    | cons i is ih => rw [Gather.collect,DescentPackedZip.work,ih,one,List.length_cons,Nat.mul_succ];omega
  simpa only [gather,Gather.assembly,List.length_finRange] using pass (List.finRange L.donors)

theorem controls_work (l : Fin L.sites) : (L.want P l).work+L.counts.work=19:=rfl

theorem labels (w : ℕ) :
    DescentStaticWordColumn.names (L.program w P old)=15*(L.volume+1)+15+244*L.donors := by
  rw [program,DescentStaticWordColumn.names_seq,ROM.mount,DescentStaticWordColumn.names_mount,
    DescentStaticWordColumn.names_scan,L.gather_work P old]
  dsimp only [volume]
  omega

def phase (w : ℕ) : NativePhase w :=
  ⟨L.program w P old,L.ticks P old,L.output P old,cheap_seq
    (ROM.cheap L.pages L.width w L.base) (scan_cheap w L.outBase L.rows (L.gather P old))⟩

theorem stepped {w} (m : Memory w)
    (access : ∀b,Accessible P (old b) L.hosts L.groups L.lanes w L.outBase)
    (limit : L.endAddress<2^w) : (L.phase P old w).Runs m :=
  (L.any P old m access limit).1

theorem syntax_clock (w : ℕ) :
    L.ticks P old + 7*DescentStaticWordColumn.names (L.program w P old) ≤
        2000*(L.volume+(L.rows+1)*(L.donors+1)+1) := by
  rw [L.labels P old w,ticks,L.gather_work P old]
  nlinarith [Nat.zero_le L.rows,Nat.zero_le L.donors,Nat.zero_le L.volume,
    Nat.zero_le (L.rows*L.donors)]

theorem immutable_size {h} (lookup : (L.roleBits*L.nodes)*L.lanes≤h/4)
    (assembly : (L.countBits*L.donors+L.countBits)*L.lanes≤h/4)
    (chunks_ : L.chunkBits≤h/4) (pages_ : L.count≤2^(h/4)) :
    L.volume≤2^(h/2) := by
  have le : L.width≤h/4:=max_le lookup (max_le assembly chunks_)
  calc L.volume ≤ 2^(h/4)*2^(h/4) := Nat.mul_le_mul pages_ (Nat.pow_le_pow_right (by decide) le)
    _ = 2^(h/4+h/4) := (pow_add ..).symm
    _ ≤ 2^(h/2) := Nat.pow_le_pow_right (by decide) (by omega)

theorem end_space : L.endAddress≤L.base+L.volume+2*(L.rows+1) := by
  dsimp only [endAddress,outBase,outBits]
  have cap : 2^Nat.clog 2 (L.rows+1)≤2*(L.rows+1) := by
    by_cases small : L.rows+1≤1
    · have zero : L.rows=0:=by omega
      simp [zero]
    · have pos : 0<Nat.clog 2 (L.rows+1):=Nat.clog_pos (by decide) (by omega)
      have lower:=Nat.pow_pred_clog_lt_self (b:=2) (x:=L.rows+1) (by decide) (by omega)
      change 2^(Nat.clog 2 (L.rows+1)-1)<L.rows+1 at lower
      rw [show Nat.clog 2 (L.rows+1)=Nat.clog 2 (L.rows+1)-1+1 by omega,pow_succ]
      omega
  exact Nat.add_le_add_left cap _

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout

end OAI
