import OAI.Hierarchy.DescentDatedActorGate
import OAI.Hierarchy.DescentPaidSweepBill

namespace OAI
/-! # Clock and printed instruction count for the dated actor gate -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentSIMDLookup DescentPackedZip DescentActorRaster DescentSharedLeafLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn (names names_scan names_seq names_mount)
open DescentPaidResidentCount.Sweep (columnBill tableBill)
noncomputable section

private theorem columns_priced (w rows base W : ℕ) (es : List Expr) (work : ∀e∈es,e.work≤W) :
    clock (ProbeStage.Native.columns rows base es) +
      7*names (ProtocolRAM.program w (ProbeStage.Native.columns rows base es)) ≤
      columnBill es.length rows W := by
  have text (xs : List Expr) (cut : ℕ) (bound : ∀e∈xs,e.work≤W) :
      names (ProtocolRAM.program w (ProbeStage.Native.columns rows cut xs))≤
        15+xs.length*(11+4*W) := by
    induction xs generalizing cut with
    | nil =>
      simp [ProbeStage.Native.columns,ProtocolRAM.program,names_scan,Expr.work]
    | cons e xs ih =>
      have head:=bound e (List.mem_cons_self ..)
      have tail:=ih (cut+rows) (fun e he=>bound e (List.mem_cons_of_mem _ he))
      simp only [ProbeStage.Native.columns,ProtocolRAM.program,Pass.procedure,names_seq,names_scan,
        List.length_cons,Nat.succ_mul] at *
      omega
  exact Nat.add_le_add (ProbeStage.Native.columns_clock rows base W es work)
    (Nat.mul_le_mul_left 7 (text es base work))

variable (v : ActorSetup) (base : ℕ) (pop : Bank) (ctrl : Fin v.shapes→Headers.Control)
    (qs : Fin v.shapes→CPU.Query) (st : Expr) (w : ℕ)

/-- Scalar header passes, the shared broadcast table, the packed gate tables,
and the packed opcode passes each pay their own clock and printed text. -/
theorem operator_tariff :
    v.operatorTime base pop ctrl qs st w + 7*names (v.operator base pop ctrl qs st (w:=w)) ≤
      columnBill v.shapes v.hosts 29 +
        tableBill (2*Public.stride v.hosts v.groups v.lanes+
          2^Nat.clog 2 (Public.words v.headerBits v.lanes)) +
        tableBill (v.shapes*(2*2^(v.unitBits*v.lanes))) +
        columnBill v.shapes (v.hosts*v.chunksPerHost) (st.work+38) := by
  let layout:=v.gate base
  let N:=v.hosts*v.chunksPerHost
  let heads:=HeaderGate.heads layout v.hosts v.groups v.lanes v.headerBits (Q:=v.shapes)
  let header:=List.ofFn fun j=>Headers.expression (v.sources pop base) (ctrl j)
  let image:=Public.literals layout.repeatBase 1 v.hosts v.groups v.lanes v.headerBits w
  let menu:=CPU.menu v.localDepth v.stencilBits v.headerBits qs
  let gates:=Book.install menu v.unitBits v.lanes w layout.gateBase
  let tabs:=Book.tables menu v.unitBits v.lanes layout.gateBase
  let es:=List.ofFn (CPU.expression tabs st heads)
  have headWork (j : Fin v.shapes) : (Headers.expression (v.sources pop base) (ctrl j)).work≤29 := by
    cases ctrl j <;> simp [Headers.expression,Headers.select,Expr.work]
  have gateWork (j : Fin v.shapes) : (CPU.expression tabs st heads j).work≤ st.work+38 := by
    unfold CPU.expression
    rw [DescentPackedZip.work]
    change st.work+27+11≤ st.work+38
    omega
  have headerCost:=columns_priced w v.hosts layout.scalar 29 header (by
    intro e he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    exact headWork j)
  have gateCost:=columns_priced w N layout.output (st.work+38) es (by
    intro e he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    exact gateWork j)
  have headerLen : header.length=v.shapes:=List.length_ofFn
  have gateLen : es.length=v.shapes:=List.length_ofFn
  rw [headerLen] at headerCost
  rw [gateLen] at gateCost
  have words : image.length=2*Public.stride v.hosts v.groups v.lanes+
      2^Nat.clog 2 (Public.words v.headerBits v.lanes) := by
    change (layout.repeatBase+2*Public.stride v.hosts v.groups v.lanes+
      2^Nat.clog 2 (Public.words v.headerBits v.lanes))-layout.repeatBase=_
    rw [Nat.add_assoc,Nat.add_sub_cancel_left]
  have gateNames : names gates=15*(v.shapes*(2*2^(v.unitBits*v.lanes))+1):=names_mount ..
  let p:=ProbeStage.Native.columns v.hosts layout.scalar header
  let s:=ProbeStage.Native.columns N layout.output es
  change clock p+(4+10*image.length)+(4+10*(v.shapes*(2*2^(v.unitBits*v.lanes)))+clock s)+
    7*names (((ProtocolRAM.program w p).seq image.program).seq (gates.seq (ProtocolRAM.program w s)))≤_
  rw [names_seq,names_seq,names_seq,image.hardware.2,gateNames,words]
  dsimp only [tableBill]
  change clock p+7*names (ProtocolRAM.program w p)≤_ at headerCost
  change clock s+7*names (ProtocolRAM.program w s) ≤
    columnBill v.shapes (v.hosts*v.chunksPerHost) (st.work+38) at gateCost
  omega

private theorem pow_clog_le_double (n : ℕ) : 2^Nat.clog 2 n≤2*n+1 :=by
  by_cases small : n≤1
  · interval_cases n <;> decide
  have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
  have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
  cases dep : Nat.clog 2 n with
  | zero=>omega
  | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega

/-- Each shape scans the hosts and their packed rows. Its lookup table is
mounted once for all hosts. -/
theorem operator_price :
    v.operatorTime base pop ctrl qs st w+7*names (v.operator base pop ctrl qs st (w:=w)) ≤
      8192*(v.shapes+1)*(st.work+1)*(1+v.hosts+v.hosts*v.chunksPerHost)+
      1024*(1+(v.lanes+1)*2^v.headerBits+v.shapes*2^(v.unitBits*v.lanes)) := by
  apply (v.operator_tariff base pop ctrl qs st w).trans
  let N:=v.hosts*v.chunksPerHost
  let R:=(v.lanes+1)*2^v.headerBits
  let P:=2^(v.unitBits*v.lanes)
  change columnBill v.shapes v.hosts 29+tableBill (2*2^Nat.clog 2 N+2^Nat.clog 2 R)+
    tableBill (v.shapes*(2*P))+columnBill v.shapes N (st.work+38)≤
    8192*(v.shapes+1)*(st.work+1)*(1+v.hosts+N)+1024*(1+R+v.shapes*P)
  have pages:=Nat.add_le_add (Nat.mul_le_mul_left 2 (pow_clog_le_double N)) (pow_clog_le_double R)
  have cheaper : tableBill (2*2^Nat.clog 2 N+2^Nat.clog 2 R)≤tableBill (2*(2*N+1)+(2*R+1)) := by
    unfold tableBill
    omega
  apply (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left cheaper _) _) _).trans
  unfold columnBill tableBill
  ring_nf
  omega

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
