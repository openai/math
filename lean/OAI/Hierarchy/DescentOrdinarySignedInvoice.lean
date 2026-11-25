import OAI.Hierarchy.DescentOrdinarySignedDate

namespace OAI
/-! Exact clock and text charges for the complete ordinary signed raster. -/
namespace Hierarchy
open DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentNextSignedWindow
open DescentPackedZip DescentParallelBase.ParentFilter DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical
noncomputable section

namespace DescentResetSignedScan.Ranks
variable {X K base b paid M H G w:ℕ}

theorem text_bound (q:Request X K) (a:Inputs X K) (lim:ℕ)
    (qLim:∀x p j,(q x p j).work≤lim) (aLim:∀x p j i,(a x p j i).work≤lim):
    DescentStaticWordColumn.names (program base b paid M H G w q a)≤
      15*(headWords b M+1)+15+count X K*(11+4*(1+K*(2*lim+12))):=by
  rw [program,DescentStaticWordColumn.names_seq]
  have head:DescentStaticWordColumn.names (DescentOrdinaryAtomFieldRAM.ROM.mount (pages b paid M) (width b M) w base)=15*(headWords b M+1):=
    DescentStaticWordColumn.names_mount ..
  rw [head,Nat.add_assoc]
  apply Nat.add_le_add_left
  apply Native.All.sweep_names
  intro i _ hi
  have ht:i<count X K:=by omega
  obtain ⟨⟨⟨x,p⟩,j⟩,eqn⟩:=(order X K).surjective ⟨i,ht⟩
  rw [←show ((order X K) ((x,p),j)).val=i from congrArg Fin.val eqn,at_query]
  let tab:=tables b paid M base (parallelQuery p)
  have each (s:Fin K):(tab.read (q x p j) (a x p j s)).work≤2*lim+11:=by
    rw [DescentPackedZip.work];have qh:=qLim x p j;have ah:=aLim x p j s;omega
  simpa [body, tab, List.length_finRange,Nat.add_assoc] using work_total _ (2*lim+11) each (List.finRange K)

end DescentResetSignedScan.Ranks

namespace DescentOrdinarySignedDate.Layout
open DescentResetSignedScan DescentOrdinarySignedAll
variable {X D Q O K L b M H G w : ℕ}
local notation "c" => breadth D*O
local notation "N" => H*chunks G M
variable (Z:Layout X (breadth D * O)) (base:ℕ)
local notation "rhead" => Ranks.headWords b M
local notation "shead" => Native.All.headWords L b M
local notation "mhead" => 32*2^(DescentResetFieldAssembler.width b M)
local notation "dhead" => Fused.TablesROM.length D Q K L b M+2*2^(DescentOrdinarySignedParents.ROM.width b M)
local notation "wr" lim => 1+c*(2*(13+11*(lim+11))+12)
local notation "ws" lim => 1+(2*c)*(14+8*((lim+18)+11))
local notation "afterROM" => DescentOrdinarySignedParents.ROM.endAddress base D Q K L b M
local notation "mid" => Tail afterROM X c b M H G

theorem clock_bound (degree lim rawLim:ℕ)
    (head:∀x j,(Z.header x j).work≤lim)
    (qs:∀x p j t,(Z.query x p j t).work≤rawLim)
    (as_:∀x p j i t,(Z.items x p j i t).work≤rawLim):
    time Z base D Q K L b M degree H G≤(8+10*dhead)+((4+10*rhead)+(4+Ranks.count X c*(4+N*(2*(wr rawLim)+4))))+
      ((4+10*mhead)+((4+10*shead)+(4+Native.All.count X L*(4+N*(2*(ws lim)+4))))):=by
  have qa:=Ranks.clock_bound (base:=afterROM) (b:=b) (paid:=b) (M:=M) (H:=H) (G:=G)
    (qword Z base D Q K L b M) (aword Z base D Q K L b M) (13+11*(rawLim+11))
    (fun x p j=>DescentOrdinarySignedParents.ROM.work base _ rawLim (qs x p j))
    (fun x p j i=>DescentOrdinarySignedParents.ROM.work base _ rawLim (as_ x p j i))
  have late:=Native.All.clock_bound (base:=DescentResetWindowTail.next mid b M) (D:=degree) (H:=H) (G:=G) (b:=b) (M:=M)
    (DescentResetWindowTail.fields mid b M L Z.header (ranks afterROM X c b M H G)) (lim+18)
    (fun x j s t=>by
      simp only [DescentResetWindowTail.fields,DescentResetFieldAssembler.fields,DescentPackedZip.work,ranks,Expr.work]
      have h:=head x (finProdFinEquiv.symm s).2;omega)
  unfold time DescentOrdinarySignedAll.time DescentResetWindowTail.time DescentOrdinarySignedParents.ROM.time
  omega

theorem text_bound (degree lim rawLim:ℕ)
    (head:∀x j,(Z.header x j).work≤lim)
    (qs:∀x p j t,(Z.query x p j t).work≤rawLim)
    (as_:∀x p j i t,(Z.items x p j i t).work≤rawLim):
    DescentStaticWordColumn.names (program Z base D Q K L b M degree H G w)≤15*(dhead+2)+
      (15*(rhead+1)+15+Ranks.count X c*(11+4*(wr rawLim)))+
      (15*(mhead+1)+(15*(shead+1)+15+Native.All.count X L*(11+4*(ws lim)))):=by
  have qa:=Ranks.text_bound (base:=afterROM) (b:=b) (paid:=b) (M:=M) (H:=H) (G:=G) (w:=w)
    (qword Z base D Q K L b M) (aword Z base D Q K L b M) (13+11*(rawLim+11))
    (fun x p j=>DescentOrdinarySignedParents.ROM.work base _ rawLim (qs x p j))
    (fun x p j i=>DescentOrdinarySignedParents.ROM.work base _ rawLim (as_ x p j i))
  have late:=Native.All.text_bound (base:=DescentResetWindowTail.next mid b M) (D:=degree) (H:=H) (G:=G) (b:=b) (M:=M) (w:=w)
    (DescentResetWindowTail.fields mid b M L Z.header (ranks afterROM X c b M H G)) (lim+18)
    (fun x j s t=>by
      simp only [DescentResetWindowTail.fields,DescentResetFieldAssembler.fields,DescentPackedZip.work,ranks,Expr.work]
      have h:=head x (finProdFinEquiv.symm s).2;omega)
  have mounted:DescentStaticWordColumn.names (DescentOrdinarySignedParents.ROM.program base D Q K L b M w)=15*(dhead+2):=by
    rw [DescentOrdinarySignedParents.ROM.program,DescentStaticWordColumn.names_seq]
    have first:DescentStaticWordColumn.names (Fused.TablesROM.program D Q K L b M base w)=15*(Fused.TablesROM.length D Q K L b M+1):=DescentStaticWordColumn.names_mount ..
    have second:DescentStaticWordColumn.names (DescentOrdinaryAtomFieldRAM.ROM.mount (DescentOrdinarySignedParents.ROM.tables D Q K L b M) (DescentOrdinarySignedParents.ROM.width b M) w (base+Fused.TablesROM.length D Q K L b M))=15*((2*2^(DescentOrdinarySignedParents.ROM.width b M))+1):=DescentStaticWordColumn.names_mount ..
    rw [first,second]
    omega
  have format:DescentStaticWordColumn.names (DescentResetFieldAssembler.program mid b M w)=15*(mhead+1):=DescentStaticWordColumn.names_mount ..
  rw [program,DescentStaticWordColumn.names_seq,mounted,DescentOrdinarySignedAll.program,DescentStaticWordColumn.names_seq,
    DescentResetWindowTail.program,DescentStaticWordColumn.names_seq,format]
  omega

end DescentOrdinarySignedDate.Layout
end
end Hierarchy

end OAI
