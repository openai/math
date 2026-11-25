import OAI.Hierarchy.TraceReceiverCofinalHalves
import OAI.Hierarchy.TraceReceiverCofinalPrices
import OAI.Hierarchy.TraceReceiverOriginalVisit
import OAI.Hierarchy.TraceReceiverRunCost

namespace OAI
/-! # The compact receiver's elected seed and stage procedures at the aligned word width -/

namespace Hierarchy.TraceReceiverCofinalVisits
open ThreeFlat Diagonal PhysicalStage HistoryContraction NavigationPass
open NativeNavigation NodePublication NavigationDirectory RAM RAM.TraceBucketAtom RAM.HistoryInitialSeed
open RAM.PhysicalProcedure RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected RAM.NavigationNodeRows
open HistoryStageSetup HistoryPartyBatchExec RAM.HistoryStageBody.Physical Diagonal.TraceBitHeader
open TickWorkspace LaneCursor Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open TraceReceiverSeedWords TraceReceiverOriginal GridRegisteredSetting HistorySelectedReceiverLoop
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] {u pc regs slots S addr k low fuel bnd : ℕ}
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
variable (I : RunData F (16*u^10) pc regs slots S addr fuel k low)
local notation "B" => I.block
local notation "M" => I.machine
local notation "fit" => I.fit
local notation "st" => I.state
local notation "hF" => I.field
local notation "hk" => I.axesFit
local notation "depth" => (k+1)+low
local notation "G" => TraceStaticRow.gateTable hF (fit).width (fit).labels addr fuel st regs slots depth
local notation "N" => TraceBitHeader.network hF (fit).width (fit).labels addr st (fit).header (fit).time regs slots depth
variable (raw dict masks gateBase : ℕ)
local notation "ids" => gateBase+FixedTraceImage.count G
local notation "shape" => bucketShape (q:=k) (low:=low) (S:=S) (f:=fuel) hF (fit).width (fit).labels addr st
    regs slots (B).cursorCopies raw dict masks ids
local notation "ROM" => (⟨raw,(N).cells,ids+(G).cells⟩ : TraceRawLookup.Layout)
local notation "off" => 1+(depth+depth)
local notation "X" => (B).cursorState hk low off (G).cells
local notation "L" => wordsLayout M fit hF st B hk
local notation "T" => forest M fit hF st B hk
local notation "U" => width M fit hF st
local notation "work" => start M fit hF st B hk
local notation "paired" => pairs M fit hF st
local notation "ins" => HistorySelectedSeedDecode.Installed (q:=k) (low:=low) (S:=S) (f:=fuel)
    hF (fit).width (fit).labels addr st (fit).header (fit).time regs slots (fit).grid raw dict masks gateBase hF
local notation "r" => I.run
local notation "C" => I.issuedCharges
local notation "J" => (TraceReceiverCofinalPrices.assembly I).steps
local notation "fee" => (B).localCoefficient*(W+1)^3

variable {axes side q d factors : ℕ} (Q : FactorPinIntervals.Layout (Cell axes side×Fin q) S factors d)
    (a : NavigationPass.Archive) (ax : k+1=a.axes) (lanes : a.remainingLanes=2^(k+1))
local notation "O" => a.cursorSeedSites B hk low off (G).cells ax lanes
variable (h : I.run.plan.History)
    (p : I.run.ArchivePath h I.issuedCharges
      (a.cursorSeedSites I.block I.axesFit low (1+(((k+1)+low)+((k+1)+low)))
        (TraceStaticRow.gateTable I.field I.fit.width I.fit.labels addr fuel I.state regs slots
          ((k+1)+low)).cells ax lanes))
    (zero : a.cursor.node=0)
local notation "lastRow" => ((r).finalArchive h C O p).1
local notation "total" => (lastRow).first+(lastRow).count
local notation "selectedNode" => (r).archiveNode h J L T C O p zero
local notation "pointer" => TraceReceiverOriginal.pin M fit hF st Q
local notation "vals" => (fun j : Fin total=>NodeValue.ofSite (selectedNode j) pointer
    (streamAt u (O).layer.count j.val) (endsAt u (O).layer.count j.val))
local notation "xs" => (r).archiveList h C O p a.seedData
variable {levels degree K heads heap : ℕ} (cur ctr : Word (16*u^10))
    (na : NodeArchive) (origin reg out issued after entry : Memory (16*u^10))
local notation "b" => na.banks
local notation "mid" => TraceReceiverWarmEntry.seen heap reg entry
variable (D : RAM.HistoryNodeDirectory.Selected.Directory (16*u^10)
      (let seed := a.cursorSeedSites I.block I.axesFit low (1+(((k+1)+low)+((k+1)+low)))
         (TraceStaticRow.gateTable I.field I.fit.width I.fit.labels addr fuel I.state regs slots
           ((k+1)+low)).cells ax lanes
       let finalLayer := (I.run.finalArchive h I.issuedCharges seed p).1
       finalLayer.first+finalLayer.count))
    (rest : Fin 1→Word (16*u^10))
include h p zero
local notation "arm" => fun j : Fin total=>(B).nativeArmTime levels fee b (numeric issued) j.val
local notation "shelf" => HistoryStageBody.Physical.archive B (TickWorkspace.base u 38) W K
local notation "fs" => families B (TickWorkspace.base u 38) W
local notation "decoder" => TraceRawLookup.virtual W ROM (TraceBucketAtom.publicProgram W)
local notation "leaf" => HistorySelectedSeed.procedure (HistoryStageBody.Physical.initial u shape) decoder
  (TraceBucketAtom.publicData shape rest)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3200000 in
theorem visits
    {directory stages budget : ℕ}
    (cache : GridPhysicalAdmission.ReceiverCache u directory stages budget heap na (O).layer xs reg out issued after)
    (store : (r).ArchiveRowsStored b (numeric issued) h C O p)
    (charged : (O).Charged b (numeric issued) work paired)
    (rootCode : ℕ→Word W) (roots : ∀ j,D.root j=rootCode
      (((r).archiveDirectory h C O p b (numeric issued) store zero (lastRow).first (lastRow).count rfl rfl).root j))
    (originalRun : (r).WordVisits (RecordedWordStep K cur ctr heads heap reg (Fin S→Bool) (B).publicTemplate) h J L C O p)
    (initial : State.HalfRows O (fun i=>a.initialRecords≤ i ∧ i<a.metadataEnd) (numeric origin))
    (seedRead : ∀ i : Fin a.initialSites,∀ c : Fin 5,origin (a.initialRecords+5*i.val+c.val)=
      ((![(a.seed),i.val,0,i.val%a.remainingLanes,i.val/a.remainingLanes] : Fin 5→ℕ) c : Word W))
    (seedFrame : ∀ z,a.initialRecords≤z→z<a.metadataEnd→ reg z=origin z)
    (headLo : TickWorkspace.base u 20≤heads) (heapHi : heap≤TickWorkspace.base u 40)
    (seedLo : TickWorkspace.base u 20≤a.initialRecords) (seedHi : a.metadataEnd≤heap)
    (stageFrame : ∀z,TickWorkspace.base u 20≤z→z<heap→entry z=reg z)
    (saved : ∀z,TickWorkspace.base u 43≤z→z<TickWorkspace.base u 45→entry z=issued z)
    (nodes : (b).nodes=TickWorkspace.base u 44) (cash : (b).charges=TickWorkspace.base u 43)
    (age : 40≤u) (fixed : (B).archiveConstant (B).localCoefficient≤u)
    (small : ∀ i : Fin ((B).shrink.more.length+1),((B).shrink.block ((B).shrink.row i)).bitCap≤V)
    (large : ∀ i : Fin ((B).refresh.last+1),((B).refresh.block i).bitCap≤V)
    (unit : 0<(b).unitWork) (peakWork : ∀i,I.work h C (b).unitWork i≤peak)
    (len : ((B).repeat I.passes).length≤levels) (allowance : (B).archiveUnit u (B).localCoefficient degree≤(b).unitWork)
    (margin : 10*(levels+2)^2*fee≤(b).unitWork)
    (owner : ℕ→Fin factors) (home : ∀i:Fin S,Q.origin i=owner (i.val/(2*2^low)))
    (roomPin : d≤2^W) (even : Even S)
    (square : total≤V^2) (chart : TickWorkspace.base u 45<2^W)
    (laneRoom : 4*(2^(k+1))≤ TickWorkspace.stride u) (axisRoom : k+1≤2^W) (lanesFit : 2^(k+1)≤2^W)
    (gateHi : TickWorkspace.base u 19≤gateBase) (dictHi : TickWorkspace.base u 19≤dict)
    (masksHi : TickWorkspace.base u 19≤ masks) (romReady : ins entry)
    (rawFit : HistorySelectedSeedDecode.Fits (q:=k) (low:=low) (S:=S) (f:=fuel) («b»:=bnd) («W»:=W)
      hF (fit).width (fit).labels addr st (fit).header (fit).time regs slots (B).cursorCopies raw dict masks gateBase)
    (offset : ∀ v : PairedCursor.Site (k+1),∀ t : 0<U v,
      entry (TickWorkspace.base u 5+4*(finFunctionFinEquiv v.2).val+3)=
        ((Q.slot (source M fit hF st v ⟨0,t⟩)).val:Word W))
    (table : Mounted B W W (TickWorkspace.base u 38) entry)
    (tableSize : TickWorkspace.base u 38+libraryWords B W<2^W)
    (stridePos : 0<K) (strideFit : K<2^W) (counters : cur.val<ctr.val) :
    ∀ (j : Fin total) prev,Ledger u D HistoryRefreshEmitter.tag vals (TickTerminalRoot.slotKeep u) entry j.val prev→picked D j.val=true→
      Emitted (u:=u) shelf leaf fs D vals HistoryRefreshEmitter.tag ((B).nativeVisitCost levels fee b (numeric issued))
        arm (fun j _=>arm j) j (bump (ownerData W u) prev) := by
  have up {i j : ℕ} (h : i≤j) : TickWorkspace.base u i≤TickWorkspace.base u j :=
    Nat.mul_le_mul_right _ (by omega)
  have cashLo : TickWorkspace.base u 43≤(b).charges := cash.ge
  have nodeLo : TickWorkspace.base u 43≤(b).nodes := (up (by decide : 43≤44)).trans nodes.ge
  have warm:=TraceReceiverWarmEntry.warm
    (cache.warm_at (archive_chronological r h C O p a.seedData) cashLo nodeLo saved) heapHi stageFrame
  have recorded:=TraceReceiverWarmEntry.visits r h J L C O p reg entry (B).publicTemplate originalRun
  have halves:=TraceCompactSeed.seen_half_rows origin reg entry initial seedFrame seedHi seedLo heapHi
  have u10 : 8≤u^10 := (by decide : 8≤40^10).trans (Nat.pow_le_pow_left age _)
  have vol : 162≤V := (by decide : 162≤2^8).trans (Nat.pow_le_pow_right (by decide) u10)
  have cap : 4*peak≤V := by
    change 2^2*2^((3*u^10+4)/5)≤2^(u^10)
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have peakRoom : peak≤V := by omega
  have word : peak<2^W := peakRoom.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  obtain ⟨resource,price⟩:=TraceReceiverCofinalPrices.native I u levels peak b (numeric issued) h O p zero unit
    len peakRoom small large charged store peakWork
  have staged:=HistorySelectedDispatch.mounted_rows B cur ctr b mid issued entry headLo heapHi unit word
    r h J L C O p a.seedData warm work paired (HistorySelectedPairWidths.exact_seed M fit hF st even)
    charged store (words_ordered M fit hF st B hk) halves recorded resource
  have endSeed : a.initialRecords+5*a.initialSites≤a.metadataEnd := by
    change _≤a.initialRecords+(7+8*a.initialDegree)*a.initialSites
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have savedKernel:=TraceReceiverOriginal.kernel_words a origin reg reg entry seedRead seedFrame
    (fun _ _ _=>rfl) (fun z lo hi=>stageFrame z (seedLo.trans lo) (hi.trans_le seedHi)) endSeed
  have cost : 2≤fee:=TraceDistribution.Physical.fresh_price_scale B u
  have coeff : (W+1)^3≤fee := Nat.le_mul_of_pos_left _ (by unfold Block.localCoefficient;omega)
  have power : V^2*V^2=TickWorkspace.stride u := by change V^2*V^2=V^4;ring
  have scratchRoom : V+42≤TickWorkspace.stride u := by
    have volumeSquare : V≤V^2 := by
      simpa only [pow_two] using Nat.le_mul_of_pos_left V (show 0<V by omega)
    rw [←power]
    exact (show V+42≤2*V by omega).trans
      (Nat.mul_le_mul ((show 2≤V by omega).trans volumeSquare) volumeSquare)
  have dirs : 8*total≤ TickWorkspace.stride u := by
    rw [←power]
    exact Nat.mul_le_mul (by nlinarith [vol] : 8≤V^2) square
  have wordTotal : total≤2^W := by
    have region:=up (by decide : 0≤45)
    change 1*TickWorkspace.stride u≤_ at region
    omega
  have header : TickWorkspace.base u 13+8*total≤TickWorkspace.base u 14 := by
    change 14*TickWorkspace.stride u+8*total≤15*TickWorkspace.stride u
    omega
  have spans (j : Fin total) : (vals j).stream+4*(vals j).net.cells≤TickWorkspace.base u 14 ∧
      (vals j).ext+(vals j).external≤TickWorkspace.base u 14 := by
    have both:=TraceReceiverRunCost.sizes (O).layer.count (selectedNode j) pointer b (numeric issued) (price j)
      (by omega) vol cost margin
    have bound : (j.val+1)*V^2≤ TickWorkspace.stride u := by
      rw [←power];exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt |>.trans square)
    have last : TickWorkspace.base u 12+(j.val+1)*V^2≤TickWorkspace.base u 14 := by
      change 13*TickWorkspace.stride u+_≤15*TickWorkspace.stride u;omega
    exact ⟨both.1.trans last,both.2.trans last⟩
  refine HistorySelectedDispatch.visits r h J L T C O p zero pointer B cur ctr b mid issued entry xs D shape ROM rest
    store rootCode roots staged warm price ?_ allowance coeff margin unit age fixed square nodes cash headLo heapHi table
    tableSize stridePos strideFit counters wordTotal ((up (by decide : 18≤45)).trans_lt chart) header
    (fun j=>(spans j).1) (fun j=>(spans j).2)
  · intro v j prev which isLeaf live _
    exact TraceReceiverOriginal.original M fit hF st B hk raw dict masks gateBase Q a ax lanes r h J C p zero b
      mid issued entry rest D owner home roomPin even unit charged warm nodes cash price cap savedKernel
      ((up (by decide : 19≤20)).trans seedLo) ((endSeed.trans (seedHi.trans heapHi)).trans_lt ((up (by decide : 40≤45)).trans_lt chart))
      chart (by omega) scratchRoom square dirs laneRoom axisRoom lanesFit gateHi dictHi masksHi
      romReady rawFit offset v j prev which isLeaf live
end
end Hierarchy.TraceReceiverCofinalVisits

end OAI
