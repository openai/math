import OAI.ThreeFlat.Diagonal.TraceJournalRecoveryGoal
import OAI.Hierarchy.TraceRefreshRetained

namespace OAI
/-! # Recover the selected refresh row and continue through the original tail -/
namespace ThreeFlat.Diagonal.NavigationPass.TraceRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

open private recoverJoinedStage recovered_drop from OAI.ThreeFlat.Diagonal.TraceJournalRecoveryGoal

variable {a : Archive} {W limit Z tariff H MCap : ℕ} {cur ctr : Word W}
    {«protected» : ℕ→Prop} {initial : Layer→Prop}
open Expander
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem recoverRefresh (s t h pad : ℕ) (g : Fin (2^s) → Fin (2^s) → ℕ) (γ cost : ℝ)
      (G : RefreshMotif.Table F g (1+h+pad) cost) (hm : 2≤2^s) (hh : 0<h)
      (sym : ∀ i j,g i j=g j i) (rows : ∀ i, ∑ j,g i j=h) (zero : ∀ i,g i i=0)
      (conn : Bound (transition g h) ℝ γ) (degree : 1+h+pad=2^t) (tail : Program F t)
    (ih : RecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial tail)
    (_room : Hierarchy.TraceRetainedRoom.Room limit W) (_wide : 8≤W) (controls : cur.val<ctr.val) :
    RecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial (.refresh s t h pad g γ cost G hm hh sym rows zero conn degree tail) := by
  intro bounds costs rem X reach c raw input final journal old num first data seed space
  let b:=tail.charge+rem
  let e:=Nat.add_assoc s tail.charge rem
  let B : State (2^s) (s+b):=e ▸ X
  let R:=refreshBinary G B hm hh sym rows zero conn
  let R':=Program.recastMove degree R
  let next:=fun j=>tail.run rem (R'.next j)
  let Q:=refreshBinaryFamily G B hm hh sym rows zero conn
  let old' := castSites e X old
  let op:=Stage.refresh (Fintype.card B.Base) (2^s) (2^b) h pad
  rcases journal with ⟨mid,out,fit,j,boot,hit,shape,localRoom,⟨oldArrays,oldStored⟩,actual,published,frame,cont⟩
  rw [shape] at space
  conv => arg 7; rw [shape]
  let k := Program.degreeTerm degree R j
  let ce : (Run.step R' next).WidthCeiling Z := Program.beforeRecast e X _ reach
  let bs : ∀ n∈tail.recordBounds,n.1≤a.K ∧ n.2*Z<2^W := fun n hn=>bounds n (List.mem_cons_of_mem _ hn)
  let cs : ∀ n∈tail.factors,n≤tariff := fun n hn=>costs n (List.mem_cons_of_mem _ hn)
  let transported:=Program.degreeFamily degree R (Fintype.card B.Base*2^b) (Fintype.card B.Base*2^s) Q fit
    rfl (refreshBinary_next_base G B hm hh sym rows zero conn)
  let qt := fun z => tail.table a.K W Z bs rem (R'.next z) (ce.2 z)
  have bv : Fintype.card B.Base=Fintype.card X.Base := Program.baseCast e X
  let stepTable : Program.RecordTable (Run.step R' next) a.K W
      ((Fintype.card X.Base*2^b)::(tail.directory rem (Fintype.card X.Base*2^s)).map Stage.motifs) :=
    Program.consTable R' next transported.1 transported.2.1
      (transported.2.2.1.trans (congrArg (fun card => card*2^b) bv))
      (fun z => (qt z).changeSizes (congrArg (fun card => (tail.directory rem card).map Stage.motifs)
        ((transported.2.2.2 z).trans (congrArg (fun card => card*2^s) bv))))
  let record : (Run.step R' next).Records :=
    ⟨transported.1.record transported.2.1,fun z=>(tail.table a.K W Z bs rem (R'.next z) (ce.2 z)).records⟩
  have selected : record.1.read (raw.take record.1.width)=some k := by
    have eq := Program.degree_read degree R _ _ Q fit rfl (refreshBinary_next_base G B hm hh sym rows zero conn) raw
    exact eq.trans (by rw [hit];rfl)
  have wid : record.1.width=(Q.record fit).width := by
    change transported.1.motifs*a.K*W=Q.motifs*a.K*W
    rw [transported.2.2.1]; rfl
  have funding (z : Fin R.rules.count) := (refreshBinaryCharge_sum G B hm hh sym rows zero conn z).trans
      (Nat.mul_le_mul_right _ (costs _ (List.mem_cons_self ..)))
  let nativeCharge : Program.siteCharge R tariff :=
    ⟨refreshBinaryCharge G B hm hh sym rows zero conn, funding⟩
  let certificate : Program.Certified (Run.step R' next) tariff :=
    Program.consCert R' next (Program.siteRecast degree R nativeCharge)
      (fun z => tail.certifiedCharges tariff cs rem (R'.next z))
  have copies (i : Fin Q.motifs) : out (c.heap+i.val*3)=(Q.copies i:Word W) := by
    simpa only [Fin.val_zero, Nat.add_zero, eq_self, ite_true] using published.1 i 0
  let following := tail.directory rem (Fintype.card (R'.next k).Base)
  have stageSpace : JournalSpace a.K W H MCap (op::following) c old.layer «protected» := space
  have here := JournalSpace.local (K:=a.K) (W:=W) (op:=op) (ops:=following) stageSpace
  obtain ⟨row,numbered,lay,ptr,reads,below,foot,parents,paddr,nSize,_⟩ :=
    Hierarchy.TraceRefreshRetained.archiveRecast G B hm hh sym rows zero conn degree c cur j _ out actual fit copies
      (localRoom.heap.trans cur.isLt.le) here.1 old' (numbered_castSites e X old num) first funding
  have caps:=stageSpace.caps op (List.mem_cons_self ..)
  have source:=rows_of_one_stage R' k old' row data op c tail rem (R'.next k) _ cont «protected» seed
    controls stageSpace.header localRoom.heap here.2 reads foot parents paddr
    (fun i=>⟨(nSize i).1.trans caps.1,(nSize i).2.trans caps.2⟩)
  have tailSpace := stageSpace.tail
  rw [←lay] at tailSpace
  have succFirst : row.sites.layer.first=(allocate a.K c op).next.node := by rw [lay];rfl
  have tailRun := ih bs cs (rem:=rem) (X:=R'.next k) (ce.2 k) (allocate a.K c op).next
    (raw.drop (Q.record fit).width) cont row.sites numbered succFirst row.data (Or.inr source.1) tailSpace
  let stageResult := stagePost a.K (op::following) c old.layer «protected»
    (fun i=>(final i).val) H MCap initial
  let pricedRow : R'.ArchiveStep k old' (certificate.1.1 k) := row
  have rest := recovered_drop (raw:=raw) wid tailRun
  have joined := recoverJoinedStage R' next record certificate.1 old' data raw k selected pricedRow
    (K:=a.K) (op:=op) (ops:=following) (c:=c) (mem:=fun i=>(final i).val)
    (H:=H) (M:=MCap) («protected»:=«protected») (initial:=initial)
    succFirst ptr lay source.2 rest
  apply recovered_recast e X (.step R' next) stepTable certificate old data raw stageResult
  exact joined


end
end ThreeFlat.Diagonal.NavigationPass.TraceRecovery

end OAI
