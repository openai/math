import OAI.Hierarchy.TraceReceiverCofinalVisits
import OAI.Hierarchy.TraceReceiverCofinalTariff
import OAI.Hierarchy.TraceReceiverDescendantExecution
import OAI.Hierarchy.TraceReceiverDescendantFrames
import OAI.Hierarchy.TraceReceiverElectedIntervals
import OAI.Hierarchy.TraceReceiverElectedJournal

namespace OAI
/-! # Visiting elected compact descendants after the native table, pin and owner mounts -/

namespace Hierarchy.TraceReceiverDescendantVisits
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
variable {F : Type} [Field F] [Fintype F] {W u pc regs slots S addr k low fuel bnd : ℕ}
local notation "V" => volume u
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
variable (I : RunData F W pc regs slots S addr fuel k low)
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
variable {levels degree K heads heap : ℕ} (cur ctr : Word W)
    (na : NodeArchive) (origin reg out issued after entry : Memory W)
local notation "b" => na.banks
local notation "mid" => TraceReceiverWarmEntry.seen heap reg entry
variable (D : RAM.HistoryNodeDirectory.Selected.Directory W
      (let seed := a.cursorSeedSites I.block I.axesFit low (1+(((k+1)+low)+((k+1)+low)))
         (TraceStaticRow.gateTable I.field I.fit.width I.fit.labels addr fuel I.state regs slots
           ((k+1)+low)).cells ax lanes
       let finalLayer := (I.run.finalArchive h I.issuedCharges seed p).1
       finalLayer.first+finalLayer.count))
    (rest : Fin 1→Word W)
include h p zero
local notation "arm" => fun j : Fin total=>(B).nativeArmTime levels fee b (numeric issued) j.val
local notation "shelf" => HistoryStageBody.Physical.archive B (TickWorkspace.base u 38) W K
local notation "fs" => families B (TickWorkspace.base u 38) W
local notation "decoder" => TraceRawLookup.virtual W ROM (TraceBucketAtom.publicProgram W)
local notation "leaf" => HistorySelectedSeed.procedure (HistoryStageBody.Physical.initial u shape) decoder
  (TraceBucketAtom.publicData shape rest)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3200000 in
theorem visits_at (aligned : W=16*u^10)
    {directory stages budget : ℕ}
    (cache : GridPhysicalAdmission.ReceiverCache u directory stages budget heap na (O).layer xs reg out issued after)
    (store : (r).ArchiveRowsStored b (numeric issued) h C O p)
    (charged : (O).Charged b (numeric issued) work paired)
    (rootCode : ℕ→Word W) (roots : ∀ j,D.root j=rootCode
      (((r).archiveDirectory h C O p b (numeric issued) store zero (lastRow).first (lastRow).count rfl rfl).root j))
    (originalRun : (r).WordVisits (RecordedWordStep K cur ctr heads heap reg (Fin S→Bool) (B).publicTemplate) h J L C O p)
    (initial : State.HalfRows O (fun i=>a.initialRecords ≤ i ∧ i<a.metadataEnd) (numeric origin))
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
  subst W
  exact TraceReceiverCofinalVisits.visits I raw dict masks gateBase Q a ax lanes h p zero cur ctr na
    origin reg out issued after entry D rest cache store charged rootCode roots originalRun initial seedRead seedFrame
    headLo heapHi seedLo seedHi stageFrame saved nodes cash age fixed small large unit peakWork len allowance margin
    owner home roomPin even square chart laneRoom axisRoom lanesFit gateHi dictHi masksHi romReady rawFit offset
    table tableSize stridePos strideFit counters
end
end Hierarchy.TraceReceiverDescendantVisits

namespace Hierarchy.TraceReceiverDescendantVisits
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction NavigationDirectory
open NativeNavigation NodePublication RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.HistoryStageBody.Physical RAM.HistoryInitialSeed
open HistoryStageSetup HistoryPartyBatchExec TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open GridRegisteredSetting HistorySelectedReceiverLoop TraceReceiverLeafSetup
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] {w pc regs slots S addr fuel axes : ℕ}
variable (I : RunData F (64*w) pc regs slots S addr fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "u" => TraceAdmission.receiverAge w
local notation "W" => (64*w)
local notation "B" => I.block
local notation "M" => I.machine
local notation "ft" => I.fit
local notation "hF" => I.field
local notation "st" => I.state
local notation "hk" => I.axesFit
local notation "d" => (axes+1)+(w/2)
local notation "G" => TraceStaticRow.gateTable hF (ft).width (ft).labels addr fuel st regs slots d
local notation "O" => (GridReceiverDirectory.archive I l).cursorSeedSites B hk (w/2) (1+(d+d)) (G).cells rfl rfl
local notation "a" => GridReceiverDirectory.archive I l
local notation "dn" => GridReceiverDirectory.native I l
local notation "stop" => finish (a).K (dn).stages (a).cursor
local notation "b" => (dn).node.banks
local notation "phase" => ((B).repeat I.passes).length
local notation "P" => GridReceiverBanks.pinPlan I l
local notation "C" => I.issuedCharges
local notation "r" => I.run
local notation "K" => (B).localCoefficient*(W+1)^3
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
local notation "L" => TraceReceiverSeedWords.wordsLayout M ft hF st B hk
local notation "trees" => TraceReceiverSeedWords.forest M ft hF st B hk
local notation "J" => (TraceReceiverCofinalPrices.assembly I).steps
local notation "T" => (l.sideMinusOne+1)^(l.dimension+1)*l.copies
local notation "full" => (2^(axes+1):ℕ)
local notation "dim" => (l.dimension+1)
local notation "g" => GridPinArena.slab w
local notation "radix" => (20*(w+1)+2)^(dim+2)
local notation "table" => TraceReceiverTablesMount.output I
local notation "fees" => I.issuedUnit w l.degree l.stageRate l.rootRate

variable {geom : GridReceiverDirectory.ElectionRoom I l} {safe : GridNativeDispatch.WordRoom I}
    {z : I.trace} {sel : Fin (l.selectorCap+1)→Bool}
    {t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)} {input origin elected : Memory (64*w)}
    (j : TraceReceiverElectedJournal.Journal I l geom safe z sel t input origin elected)
    (Q : FactorPinIntervals.Layout (Cell (l.dimension+1) l.sideMinusOne×Fin l.copies) S (I.roots z.1) l.pinWidth)
local notation "last" => ((r).finalArchive z.1 C O j.path).1
local notation "total" => (last).first+(last).count
local notation "costs" => I.costs (GridNativeImage.resources I l) z.1 l.dimension l.sideMinusOne l.bank C fees
local notation "price" => (fun i : Fin (last).count => costs (i.cast j.card.symm))
local notation "owners" => (fun i : Fin (last).count => ((FactorAllocation.owner geom.teams_pos w price i).val:Word W))
local notation "chron" => (r).archiveDirectory z.1 C O j.path b (numeric j.saved) j.stored rfl (last).first (last).count rfl rfl
local notation "D" => TraceReceiverOwnerMount.directory chron owners (t.val:Word W)
local notation "node" => (r).archiveNode z.1 J L trees C O j.path rfl
local notation "ptr" => TraceReceiverOriginal.pin M ft hF st Q
local notation "val" => (fun i : Fin total=>NodeValue.ofSite (node i) ptr (streamAt u (O).layer.count i.val)
    (endsAt u (O).layer.count i.val))
local notation "entry" => TraceReceiverDescendantExecution.entry I (last).first (last).count P elected
local notation "arm" => (fun i : Fin total=>(B).nativeArmTime phase K b (numeric j.saved) i.val)

include j in
/-- Recover every owner key needed to frame the two prefix loops, directly from the
authentic registered resources on the same elected branch, then the mounted table frame. -/
theorem «prefix» (big : 64^10≤w) (source : ∀ i,Q.origin i=I.origin z.1 i)
    (R : GridPinArena.Scalars W P S full radix g)
    (small : GridPinArena.Small w P S full ((dn).stages.length*full) radix)
    (lib : libraryWords B W≤ TickWorkspace.stride u)
    (frame : TraceReceiverEntryTables.TableFrame w u (libraryWords B W) elected (table elected)) :
    GridPinPublisher.PrefixOwners P (table elected) := by
  have raw:=GridReceiverIntervalInputs.from_prefix I l geom big z sel safe j.histories t j.assigned j.ticked Q source
  have times:=TraceAdmission.receiverAge_chart w big
  have sector:=TraceReceiverOwnerMount.sector geom.pos times.2
  have slabs:=(GridPinArena.scales w geom.pos).1
  have stagedRoom := small.staged
  have fu:=(small.full)
  have cur:=GridReceiverIntervalInputs.keep_window I l geom z Q raw (fun i lo hi=>by
    apply frame i (by omega)
    right
    change 39*TickWorkspace.stride u+libraryWords B W ≤ i
    omega)
  have actual : P=GridPinPublisher.canonical w dim l.sideMinusOne l.copies l.pinWidth
      (GridNativeImage.parameterCount I l) (l.selectorCap+1) l.receiverText l.bank
      (GridControllerSimGeometry.railCount l.dimension l.sideMinusOne l.bank)
      S (I.roots z.1) (dn).stages.length full (2*2^(w/2)) := by
    rw [GridReceiverDirectory.roots I l z.1];rfl
  rw [actual] at R cur ⊢
  exact TraceReceiverEntryTables.prefix_owners R cur

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
/-- The cost certificate and compiler visit share the exact journal witness and saved S43/S44
memory. Input slots are read after the mounted image, prefix and owner passes. -/
theorem visits (aligned : W=16*u^10) (big : 64^10≤w) (depthFit : d≤2*w+1)
    (bound : total≤2^(3*w/5)) (held : (stop).heap≤(a).control+64)
    (metadata : (a).metadataEnd≤(a).cursor.heap)
    (rev : State.HalfRows O (fun i=>(a).initialRecords ≤ i ∧ i<(a).metadataEnd) (numeric origin))
    (seed : ∀ i : Fin (a).initialSites,∀ c : Fin 5,origin ((a).initialRecords+5*i.val+c.val)=
      ((![(a).seed,i.val,0,i.val%(a).remainingLanes,i.val/(a).remainingLanes] : Fin 5→ℕ) c : Word W))
    (R : GridPinArena.Scalars W P S full radix g)
    (small : GridPinArena.Small w P S full ((dn).stages.length*full) radix)
    («prefix» : GridPinPublisher.PrefixOwners P (table elected))
    (source : ∀ i,Q.origin i=I.origin z.1 i)
    (offset : ∀ i : Fin S,(P).bucketed (table elected) ((P).source.blocks+i.val/(P).source.span)+
      ((i.val%(P).source.span:ℕ):Word W)=((GridPinAddressImage.code (Q.address i)).val:Word W))
    (librarySize : libraryWords B W≤ TickWorkspace.stride u)
    (image : TraceReceiverTablesMount.installed I (table elected))
    (library : Mounted B W W (start w) (table elected))
    (frame : TraceReceiverEntryTables.TableFrame w u (libraryWords B W) elected (table elected))
    (rawFit : HistorySelectedSeedDecode.Fits (q:=axes) (low:=w/2) (S:=S) (f:=fuel) («b»:=4*w+2) («W»:=W)
      hF (ft).width (ft).labels addr st (ft).header (ft).time regs slots (B).cursorCopies 0 (dict I) (masks I) (gateBase I))
    (pinRoom : l.pinWidth≤2^W) (even : Even S)
    (age : 40≤u) (fixed : (B).archiveConstant (B).localCoefficient≤u)
    (shrink : ∀ i : Fin ((B).shrink.more.length+1),((B).shrink.block ((B).shrink.row i)).bitCap≤volume u)
    (refresh : ∀ i : Fin ((B).refresh.last+1),((B).refresh.block i).bitCap≤volume u)
    (unit : 0<fees) (paid : ∀ i,I.work z.1 C fees i≤2^(3*w/5))
    (allowance : (B).archiveUnit u (B).localCoefficient l.degree≤fees)
    (margin : 10*(phase+2)^2*K≤fees) (alphabet : (a).K<2^W) :
    (∀ i : Fin total,Run.PricedAt b (numeric j.saved) K phase peak i.val (node i)) ∧
    ∀ i : Fin total,∀ mem,Ledger u D HistoryRefreshEmitter.tag val (TickTerminalRoot.slotKeep u) entry i.val mem→
      picked D i.val=true→Emitted («u»:=u) (bank I l) (TraceReceiverDescendantExecution.leaf I)
        (families B (start w) W) D val HistoryRefreshEmitter.tag ((B).nativeVisitCost phase K b (numeric j.saved))
        arm (fun i _=>arm i) i (bump (ownerData W u) mem) := by
  have pos:=geom.pos
  have wide : 2≤w := (by decide : 2≤64^10).trans big
  obtain ⟨lower,upper⟩:=TraceAdmission.receiverAge_chart w big
  have scales:=GridPinArena.scales w pos
  have sector:=TraceReceiverOwnerMount.sector pos upper
  have room:=TraceReceiverOwnerMount.native_room pos (by omega : 3*w≤u^10) upper bound
  have hw:=TraceReceiverLeafSetup.archive_bounds I l (by omega) held
  have tableSpan : start w+libraryWords B W≤base u 43 := by change 39*TickWorkspace.stride u+_≤44*TickWorkspace.stride u;omega
  have high : start w+libraryWords B W≤gateBase I := by
    change 39*TickWorkspace.stride u+_≤26*GridDescription.sector w;omega
  obtain ⟨rom,installed,low,pub⟩:=entry_tables I l R «prefix» room wide upper small.bits hw.2.1
    tableSpan image library frame high
  have peakLe : peak≤volume u := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have grow : 2^(3*w/5)≤peak := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have work (i) : I.work z.1 C (b).unitWork i≤peak := (paid i).trans grow
  have billed:=TraceReceiverCofinalPrices.native I u phase peak b (numeric j.saved) z.1 O j.path rfl
    unit le_rfl peakLe shrink refresh j.charged j.stored work
  refine ⟨?_,?_⟩
  · simpa only [←aligned] using billed.2
  have square : total≤(volume u)^2 := by
    apply bound.trans
    change 2^_≤(2^(u^10))^2
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have into : I.roots z.1≤ TickWorkspace.stride u := by
    rw [j.card]
    apply (Nat.le_add_left ..).trans (bound.trans ?_)
    change 2^_≤(2^(u^10))^4
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have electedAt:=election_keeps (w:=w) geom.teams_pos costs t j.reg j.classified elected j.assigned j.ticked into pos upper
  have horizon : base u 40≤base u 45 := Nat.mul_le_mul_right _ (by decide)
  have down : base u 20≤base u 43 := Nat.mul_le_mul_right _ (by decide)
  have stage (i : ℕ) (lo : base u 20 ≤ i) (hi : i<(stop).heap) : entry i=j.mid i :=
    (low i lo hi).trans ((electedAt i lo (hi.trans_le (hw.2.2.trans horizon))).trans (j.cache.stage_cells i hi))
  have saved (i : ℕ) (lo : base u 43 ≤ i) (hi : i<base u 45) : entry i=j.saved i :=
    (pub i lo hi).trans ((electedAt i (down.trans lo) hi).trans (j.savedAt i lo hi))
  let home (ordinal : ℕ) := I.dest z.1 (⟨ordinal%full,Nat.mod_lt _ (Nat.two_pow_pos _)⟩:Fin full)
  have same (i : Fin S) : Q.origin i=home (i.val/(2*2^(w/2))) := by
    rw [source i,←I.owns z.1 i]
    apply congrArg (I.dest z.1)
    apply Fin.ext
    have valEq : (I.bucket i).val=i.val/(2*2^(w/2)) :=
      TraceDistribution.native_interval_index M ft hF st i
    change (I.bucket i).val=(i.val/(2*2^(w/2)))%full
    rw [←valEq,Nat.mod_eq_of_lt (I.bucket i).isLt]
  have laneRoom : 4*full≤ TickWorkspace.stride u := by
    change 2^2*2^(axes+1)≤(2^(u^10))^4
    rw [←pow_add,←pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have chart : base u 45<2^W := by change 46*TickWorkspace.stride u<_;omega
  have laneFit : full≤2^W := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have axisFit : axes+1≤2^W := (show axes+1≤2^(axes+1) from Nat.lt_two_pow_self.le).trans laneFit
  have cg : base u 19≤gateBase I := by change 20*TickWorkspace.stride u≤26*GridDescription.sector w;omega
  have cd : base u 19≤dict I := by change 20*TickWorkspace.stride u≤27*GridDescription.sector w;omega
  have cm : base u 19≤ masks I := cd.trans (Nat.le_add_right ..)
  have hp : base u 20≤(stop).header := by rw [header_finish];exact hw.1.trans (Nat.le_add_right ..)
  have sp : base u 20≤(a).initialRecords := Nat.le_add_right ..
  have ep : (a).metadataEnd≤(stop).heap := by rw [heap_finish];exact metadata.trans (Nat.le_add_right ..)
  have lim : (a).control+1<2^W := by
    change 21*TickWorkspace.stride u+6*(2^w)^4+1<_
    have h : (2^w)^4≤ TickWorkspace.stride u := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : w≤u^10)) 4
    have nonzero : 0< TickWorkspace.stride u := by unfold TickWorkspace.stride;positivity
    omega
  have cnt : ((a).control:Word W).val<(((a).control+1:ℕ):Word W).val := by
    rw [Fin.val_cast_of_lt (by omega : (a).control<2^W),Fin.val_cast_of_lt lim]
    omega
  have libSpace : start w+libraryWords B W<2^W := by change 39*TickWorkspace.stride u+_<_;omega
  exact visits_at I 0 (dict I) (masks I) (gateBase I) Q a rfl rfl z.1 j.path rfl
    ((a).control:Word W) (((a).control+1:ℕ):Word W) (dn).node origin j.mid j.out j.saved j.reg entry
    D (rest I) aligned j.cache j.stored j.charged (fun n=>(n:Word W)) (fun _=>rfl)
    (j.visits (Fin S→Bool) L) rev seed j.initialWords hp hw.2.2 sp ep stage saved rfl rfl
    age fixed shrink refresh unit work le_rfl allowance margin home same pinRoom even square chart laneRoom
    axisFit laneFit cg cd cm rom rawFit (TraceReceiverElectedIntervals.first I l (z:=z) (elected:=elected)
      Q big room R small offset) installed libSpace (B).alphabetCap_pos alphabet cnt

end
end Hierarchy.TraceReceiverDescendantVisits

end OAI
