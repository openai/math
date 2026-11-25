import OAI.Hierarchy.GridPhysicalRootCount
import OAI.Hierarchy.GridPhysicalSelectorOrder
import OAI.Hierarchy.GridPhysicalAdmission
import OAI.Hierarchy.TraceAdmissionRecoveryScale
import OAI.Hierarchy.TraceResourceNodeRegistration
import OAI.ThreeFlat.Diagonal.TraceNodePublish
import OAI.Hierarchy.TraceResourceGridScale
import OAI.Hierarchy.TraceNodeBankAdmission

namespace OAI
/-! # The deterministic registration procedure on the actual terminal guard output -/
namespace Hierarchy.GridPhysicalAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication Filter
open scoped Classical Topology Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- Finite archive conditions obtained from the executed seed and the public placement. -/
structure RecoveryRoom (w : ℕ) (a : Archive) (ss : List Stage) (cap : ℕ) (origin : Memory (64*w)) : Prop where
  large : 7≤w
  counters : (a.control:Word (64*w)).val<((a.control+1:ℕ):Word (64*w)).val
  reads : a.seedData.Reads (natural origin)
  footprint : a.seedData.Footprint (fun z=>a.initialRecords≤z ∧ z<a.metadataEnd) (natural origin)
  halves : 2*a.initialDegree≤cap
  seedStart : (finish a.K ss a.cursor).header≤a.initialRecords
  seedEnd : a.metadataEnd≤a.cursor.heap
  curRoom : a.cursor.heap≤(a.control:Word (64*w)).val
  headRoom : (finish a.K ss a.cursor).header≤a.cursor.heap
  nodeRoom : a.cursor.node+a.seedLayer.count+(ss.map Stage.nodes).sum+(ss.map successors).sum≤2^(64*w)
  denseRoom : (finish a.K ss a.cursor).header≤a.cursor.dense

theorem register_post_using {u s : ℕ→ℕ} (scale : Scale u s) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words k size base fuel : ℕ} (hk : 2≤k+1)
      (axis : k+1=u w+1-w/2) (hp : pc≤64*w) (hr : regs≤64*w) (hs : words≤64*w)
      (machine : Machine (64*w) pc regs words) (fit : NativeTrace.Fits machine size base ((k+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (reps : B.blockCharge*s w≤k+1)
      (cap static dirs band dep setup maps : ℕ) (directions : dirs≤w)
      (bandWidth : band ≤ size) (externalPairs : 2*(dirs*band) ≤ size)
      (depSize : dep≤coef*(w+1)^exp) (setupSize : setup≤coef*(w+1)^exp) (mapSize : maps≤coef*(w+1)^exp)
      (source : ℕ→Bool) (input origin out : Memory (64*w)),
      let W:=64*w
      let depth:=(k+1)+w/2
      let grid:=TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words depth
      let off:=1+(depth+depth)
      let a:=TraceSeedWriter.archive B w (k+1) off grid.cells cap static
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let split : k+1=P.charge+rem := by dsimp only [P,rem];rw [B.charge_repeat];omega
      let X:=B.cursorState hk (w/2) off grid.cells
      let Y : State (2^B.exponent 0) (P.charge+rem):=split ▸ X
      let ss:=P.directory rem (k+1)
      let last:=TraceRecovery.lastLayer a.K ss a.cursor a.seedLayer
      let r:=Physical.nativeRun B hk machine fit hF st (s w) reps
      let C:=(Physical.registerOnLanes B (Fin size→Bool) (s w) rem X split).2
      let O:=a.cursorSeedSites B hk (w/2) off grid.cells rfl rfl
      let start:=TraceReceiverSeedWords.start machine fit hF st B hk
      let pairs:=TraceReceiverSeedWords.pairs machine fit hF st
      let desc:=TraceSourceOwner.shape W pc regs words size fuel depth grid.internal
      let trace:=TraceBitHeader.seedTraceWork (w/2) desc.stride grid.cells B.cursorCopies depth
      let unit:=FactorWork.archiveTariff w dep setup maps P.length B.localCoefficient
      let node:=traceArchive w (2^(k+1)) (2^(w/2)) ((size+1)/2) trace unit
        (directoryCap B) (directoryCap B) (directoryCap B)
      let p:=Resources.gridRows w (2^(k+1)) last.count dirs (2^(w/2)) band size node.banks.charges last.first
      let hdr:=a.control+64
      let dst:=14*2^(32*w)
      let D:=traceLimit w+ss.length*p.lanes
      ∀ enough : B.repeatFactor*(X.maxWidth+1)*B.widthBase^(s w)<2^W,
        let inner:=B.recordTable B.alphabetCap W (s w) rem Y le_rfl
          (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact enough)
        let table:=physicalTable B hk (w/2) off grid.cells (s w) W reps enough
        ∀ (extra : Memory W → ∀ h : r.plan.History, r.ArchivePath h C O → Prop),
          (∀ mid : Memory W,
            let raw:=List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val)
            a.TraceJournal (2^w) (a.control:Word W) ((a.control+1:ℕ):Word W) P rem Y a.cursor raw origin mid →
            RecoveryRoom w a ss (directoryCap B) origin →
            ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O),
              r.plan.read table.codes raw=some (h,suffix) ∧ r.FinalNumbered h C O path ∧
              TraceRecovery.stagePost a.K ss a.cursor a.seedLayer (·<(finish a.K ss a.cursor).heap) (natural mid)
                (directoryCap B) (directoryCap B) (fun _=>False) (r.archiveList h C O path a.seedData)
                (r.finalArchive h C O path).1 ∧ extra mid h path) →
        Post a P rem Y inner.records (2^w) (2^(3*w/5)) source input origin out →
        ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O)
          (count : Fintype.card (r.plan.finish h).Site=p.roots),
          r.plan.read table.codes (List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val))=some (h,suffix) ∧
          r.FinalNumbered h C O path ∧
          (∃ mid, out=TerminalWireArchive.image (a.terminal ss (P.finalEdges rem (k+1)) W) mid ∧ extra mid h path) ∧
          let idx:=Resources.indexEquiv r h count
          let dest:=fun j=>idx (r.plan.destination h (initialLane (Nat.succ_pos k) j))
          let work:=fun v=>unit*r.chargeAt h C start (idx.symm v)
          (Resources.registerNodes W (compactControl w) hdr (traceLimit w) a.cursor.header ss.length
            dst node O.layer p).Spec (·=out)
            (fun _ after=>Resources.Registered D dst p dest work after ∧
              (∀ z, z<a.seed → (z<dst ∨ dst+Resources.resourceLength p≤z) → after z=input z) ∧
              ∃ saved : Memory W, O.Charged node.banks (natural saved) start pairs ∧
                r.ArchiveRowsStored node.banks (natural saved) h C O path ∧
                (∀ z,p.charges≤z → z<traceLimit w → after z=saved z) ∧
                (∀ z,a.seed≤z → z<hdr → after z=out z) ∧
                TraceRecovery.stagePost a.K ss a.cursor a.seedLayer (·<hdr) (natural out)
                  (directoryCap B) (directoryCap B) (fun _=>False)
                  (r.archiveList h C O path a.seedData) (r.finalArchive h C O path).1 ∧
                MountedAt (natural out) a.K ss a.cursor) (2*2^(3*w/5)) := by
  have ur := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  have sr := (tendsto_order.mp scale.blocks).2 1 (by norm_num)
  filter_upwards [eventual_recovery_geometry B scale,eventual_iteration_limits B scale,eventual_node_admission B scale,
    eventual_native_archive_fits B scale coef exp,Resources.eventual_grid_layout scale (B.levels+1),
    eventual_native_port_count (F:=F) scale,TraceSeedWriter.eventual_fits B scale (3*5*10^26*65^14) 15,
    ur,sr,eventually_ge_atTop (Fintype.card F+7)] with w geometry iteration admission fitted layout
    ports seedFit uNear sNear wr
  intro pc regs words k size base fuel hk axis hp hr hs machine fit hF st reps cap static dirs band
    dep setup maps directions bandWidth externalPairs depSize setupSize mapSize source input origin out
    W depth grid off a P rem split X Y ss last r C O start pairs desc trace unit node p hdr dst D enough inner table extra choose post
  have hw : 7≤w := by omega
  have realPos : (0:ℝ)<w := by exact_mod_cast (by omega : 0<w)
  have uBound : u w≤2*w := by exact_mod_cast ((div_lt_iff₀ realPos).mp uNear).le
  have eqAxes : w/2≤u w+1 := by omega
  have sBound : s w≤w := by exact_mod_cast (by simpa using ((div_lt_iff₀ realPos).mp sNear).le : (s w:ℝ)≤w)
  have epochs : k+1=P.charge+rem := split
  have room:=trace_sector (w:=w) (by omega)
  obtain ⟨minSector,midSector,wordRoom⟩:=room
  have sector:=(sector_placement_room (w:=w) (by omega)).2
  have placed:=TraceSeedWriter.archive_placement B w (k+1) off grid.cells cap static
  have bankSpace : ArchivePlacement a (traceBase w) w := placed
  have parentCtl : ((a.control:Word W)).val=a.control := Fin.val_cast_of_lt (by
    rw [placed.control]; dsimp only [W,traceBase] at *;omega)
  have secondCtl : (a.control:Word W).val<((a.control+1:ℕ):Word W).val := by
    rw [parentCtl,Fin.val_cast_of_lt (by rw [placed.control];dsimp only [W,traceBase] at *;omega)]
    omega
  have old:=geometry axis reps a bankSpace rfl rfl rfl rfl (a.control:Word W) parentCtl
  obtain ⟨halves,seedStart,seedEnd,curRoom,headRoom,nodeRoom,lastRoom⟩:=old
  have baseEq : Fintype.card Y.Base=k+1 := (Program.baseCast split X).trans (Fintype.card_fin _)
  obtain ⟨initVisit,readSeed,footprint,keep,mid,⟨journal,ending⟩,image⟩:=post
  let short:=List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val)
  have it:=iteration (reps.trans_eq axis) a (traceBase w) 0 (a.control:Word W) rfl bankSpace parentCtl
  rw [←axis] at it
  have dense : (finish a.K ss a.cursor).header≤a.cursor.dense := by
    have tape:=it.tables
    rw [Archive.directory_length] at tape
    change a.seed+64*(ss.length+2)≤a.cursor.dense at tape
    rw [header_finish,it.origin]
    omega
  obtain ⟨h,suffix,path,decoded,numbered,seen,bonus⟩:=choose mid journal
    ⟨hw,secondCtl,readSeed,footprint,halves,seedStart,seedEnd,curRoom,headRoom,nodeRoom,dense⟩
  have dir:=compact_source_mounted P rem Y source short journal initVisit rfl
    (by simpa only [baseEq] using headRoom) curRoom secondCtl
  rw [baseEq] at dir
  let x:=a.terminal ss (P.finalEdges rem (k+1)) W
  have img : out=TerminalWireArchive.image x mid := by simpa only [baseEq] using image
  have past : a.cursor.header+64*ss.length≤x.prefixBase := by
    have g := (show (finish a.K ss a.cursor).header≤a.cursor.heap from headRoom)
    rw [header_finish] at g
    change _≤(finish a.K ss a.cursor).heap
    rw [heap_finish];omega
  have later:=Resources.after_terminal_guard (H:=hdr) x ss a.cursor a.seedLayer
    (r.finalArchive h C O path).1 (r.archiveList h C O path a.seedData) mid seen dir past lastRoom
  rw [←img] at later
  have publicCount:=Resources.final_layer_count r h C O path last later.1.2.1
  change Fintype.card (r.plan.finish h).Site=p.roots at publicCount
  refine ⟨h,suffix,path,publicCount,decoded,numbered,⟨mid,img,bonus⟩,?_⟩
  intro idx dest work
  have small:=ports hp hr hs axis machine fit hF st
  have seeds:=seedFit a (traceBase w) (P.finalEdges rem (k+1)) k off grid.cells reps axis
    rfl rfl rfl rfl small rfl placed sector
  have wordsFit:=TraceSeedWriter.layer_words seeds placed.node rfl rfl
  have hdrLo : hdr+22≤compactControl w := by
    rw [show hdr=a.control+64 from rfl,placed.control]
    change _≤traceBase w+7*traceUnit w
    have h128 : 128≤(2^w)^4 := by
      rw [←pow_mul];exact Nat.pow_le_pow_right (n:=2) (by decide) (show 7≤w*4 by omega)
    dsimp only [traceBase,traceUnit] at *;omega
  have seenNode:=later.1.transfer (protected':=(·<compactControl w)) (mem':=natural out)
    (fun _ _=>rfl) (fun z hz=>by omega)
  obtain ⟨runRoom,tape,scan,bank,pastEnds,chargeTop,time⟩:=admission machine fit axis hk le_rfl reps a placed wordsFit
    trace unit (directoryCap B) (directoryCap B) out _ _ seenNode later.2
  have lengthBound : (k+1)+w/2≤64*w := by omega
  have covered:=fitted machine fit hF st hk rem split le_rfl (by omega) hp hr hs
    lengthBound (by omega) (by omega) sBound h dep setup maps depSize setupSize mapSize
  have actualSeed:=TraceReceiverSeedWords.seedRows machine fit hF st B hk a rfl rfl rfl rfl node.banks rfl rfl rfl rfl
  have chargeEnd : node.banks.charges+2*(last.first+last.count)≤traceLimit w := by
    simpa only [later.1.2.1] using chargeTop
  obtain ⟨row,hit,physical⟩:=TraceRecovery.lastLayer_mem a.K ss a.cursor a.seedLayer
  have roots : last.count≤(k+1)*2^(k+1) := by
    have h:=program_site_count P a.K rem (k+1) a.cursor a.seedLayer
      (by rw [←epochs,wordsFit.count]) row hit
    simpa only [←epochs,physical] using h
  have publicStages : ss.length=(B.levels+1)*(s w) := (P.directory_length rem (k+1)).trans (Physical.repeated_stages B (s w))
  have stageBound : ss.length≤(B.levels+1)*(s w+1) := by rw [publicStages];exact Nat.mul_le_mul_left _ (by omega)
  have fullSize : size≤p.lanes*(2*p.pairSpan) := by
    have gridCap:=fit.grid
    change size≤2^(k+1)*(2*2^(w/2))
    rw [show 2^(k+1)*(2*2^(w/2))=2^(1+((k+1)+w/2)) by rw [pow_add,pow_add];ring]
    omega
  have sizeSmall : size≤2^(32*w) := by
    have depthMax : 1+((k+1)+w/2)≤32*w := by omega
    exact (Nat.le_add_right size fuel).trans (fit.grid.trans (Nat.pow_le_pow_right (by decide) depthMax))
  have wordLimit:=wordRoom
  have headerBefore : a.cursor.header+64*ss.length≤hdr := past.trans lastRoom
  have span : compactControl w+44≤traceLimit w := by
    change traceBase w+7*traceUnit w+44≤traceLimit w
    omega
  have layoutHeader : hdr+22 ≤ traceLimit w :=
    hdrLo.trans ((Nat.le_add_right (compactControl w) 44).trans span)
  have layoutDirectory : a.cursor.header+44+64*ss.length ≤ traceLimit w := by
    calc
      a.cursor.header+44+64*ss.length = (a.cursor.header+64*ss.length)+44 := by omega
      _ ≤ hdr+44 := Nat.add_le_add_right headerBefore 44
      _ ≤ compactControl w+44 := Nat.add_le_add_right (by omega : hdr ≤ compactControl w) 44
      _ ≤ traceLimit w := span
  obtain ⟨ps,links,rs,price,target⟩:=layout (k+1) last.count dirs ss.length (2^(w/2)) band size
    node.banks.charges last.first hdr a.cursor.header axis (by omega) roots directions stageBound
    (Nat.pow_le_pow_right (by decide) (by omega)) bandWidth sizeSmall chargeEnd layoutHeader layoutDirectory
  have stageLive:=successors_live P rem (k+1) (by omega)
  have original (j : Fin p.lanes) : (O.ord (initialLane (Nat.succ_pos k) j)).val=j.val := by
    exact (a.cursor_zero B hk (w/2) off grid.cells rfl rfl ((CompressorPacking.Native.tagOrdinal (k+1)).symm j)).trans
      (congrArg Fin.val ((CompressorPacking.Native.tagOrdinal (k+1)).apply_symm_apply j))
  have bandRoom : p.directions*p.band≤p.lanes*p.pairSpan := by
    change dirs*band≤2^(k+1)*2^(w/2)
    change size≤2^(k+1)*(2*2^(w/2)) at fullSize
    rw [show 2^(k+1)*(2*2^(w/2))=2*(2^(k+1)*2^(w/2)) by ring] at fullSize
    omega
  let snapshot := NodePublication.state node (NodePublication.program (r.archiveList h C O path a.seedData))
    (Resources.mounted (compactControl w)
      (Resources.nodeWords (compactControl w) node ss.length a.cursor.header O.layer) out) (ss.length+1)
  have proc : (Resources.registerNodes W (compactControl w) hdr (traceLimit w) a.cursor.header
      ss.length dst node O.layer p).Spec (·=out)
      (fun _ result => Resources.Registered D dst p dest work result ∧
        (∀ z, z<hdr → (z<dst ∨ dst+Resources.resourceLength p≤z) → result z=out z) ∧
        ∃ saved : Memory W, saved=snapshot ∧ O.Charged node.banks (natural saved) start pairs ∧
          r.ArchiveRowsStored node.banks (natural saved) h C O path ∧
          ∀ z, p.charges≤z → z<traceLimit w → (z<dst ∨ dst+Resources.resourceLength p≤z) →
            result z=saved z)
      (43+(compactTicks (compactControl w) (ss.length+1) (rowBudget W node ((k+1)*2^(k+1)))+
        Resources.registrationTicks hdr (hdr+5) ss.length p)) :=
    Resources.registerNodes_selected r h C O path a.seedData numbered node start pairs a.K
      (compactControl w) (rowBudget W node ((k+1)*2^(k+1))) (compactControl w) hdr
      (traceLimit w) dst (directoryCap B) (directoryCap B) ss a.cursor out p publicCount
      (initialLane (Nat.succ_pos k)) original later.1 scan (by omega) later.2 stageLive bank
      (bank.counter.1.trans (bank.counter.2.le.trans wordLimit.le)) le_rfl le_rfl rfl actualSeed covered
      runRoom tape ps links rs hdrLo headerBefore rfl rfl chargeEnd
      (target.trans (Nat.le_add_right ..)) fullSize bandRoom
  have len : (records (r.archiveList h C O path a.seedData)).length=ss.length+1 := by
    change (TraceRecovery.records (r.archiveList h C O path a.seedData)).length=ss.length+1
    rw [later.1.1,nodeLayers_length]
  rw [len] at time
  change 43+compactTicks (compactControl w) (ss.length+1) (rowBudget W node ((k+1)*2^(k+1))) ≤ 2^(3*w/5) at time
  change Resources.registrationTicks hdr (hdr+5) ss.length p ≤ 2^(3*w/5) at price
  change dst+Resources.resourceLength p ≤ traceBase w at target
  intro labels regs slots
  refine Procedure.Spec.mono (A:=Resources.registerNodes W (compactControl w) hdr (traceLimit w)
    a.cursor.header ss.length dst node O.layer p) proc (fun _ e=>e) ?_ (by
      simpa only [Nat.add_assoc,two_mul] using (Nat.add_le_add time price))
  intro ticks result published
  have frame := published.2.1
  let saved : Memory W := Classical.choose published.2.2
  have stored := Classical.choose_spec published.2.2
  have high := stored.2.2.2
  refine ⟨published.1,?_,saved,stored.2.1,stored.2.2.1,?_,?_,later.1,later.2⟩
  · intro z low free
    have phaseRoom : a.seed≤hdr := by dsimp only [hdr];rw [placed.seed,placed.control];omega
    have guardFrame : out z=mid z := by
      rw [img];simp [TerminalWireArchive.image,fillSegment,
        Nat.not_le_of_lt (show z<x.prefixBase by
          change z<(finish a.K ss a.cursor).heap
          rw [heap_finish];rw [placed.seed] at low;rw [placed.heap];omega)]
    have seedControl : a.seed≤(a.control:Word W).val := by
      rw [parentCtl,placed.seed,placed.control]
      exact Nat.le_add_right ..
    have belowControl : z<(a.control:Word W).val := low.trans_le seedControl
    have jour:=Archive.TraceJournal.frame P rem Y a.cursor short journal
      belowControl.ne (belowControl.trans secondCtl).ne
      (show traceOutsideWrites a.K a.cursor (P.directory rem (Fintype.card Y.Base)) z from
        ⟨.inl (by rw [placed.header];rw [placed.seed] at low;omega),
         .inl (by rw [placed.heap];rw [placed.seed] at low;omega)⟩)
    exact (frame _ (low.trans_le phaseRoom) free).trans (guardFrame.trans (jour.trans (keep _ low)))
  · intro z lower upper
    apply high z lower upper (.inr _)
    exact target.trans ((Nat.le_add_right (traceBase w) (12*traceUnit w)).trans lower)
  · intro z lower upper
    exact frame z upper (.inr (target.trans lower))

theorem register_post {u s : ℕ→ℕ} (scale : Scale u s) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words k size base fuel : ℕ} (hk : 2≤k+1)
      (axis : k+1=u w+1-w/2) (hp : pc≤64*w) (hr : regs≤64*w) (hs : words≤64*w)
      (machine : Machine (64*w) pc regs words) (fit : NativeTrace.Fits machine size base ((k+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (reps : B.blockCharge*s w≤k+1)
      (cap static dirs band dep setup maps : ℕ) (directions : dirs≤w)
      (bandWidth : band ≤ size) (externalPairs : 2*(dirs*band) ≤ size)
      (depSize : dep≤coef*(w+1)^exp) (setupSize : setup≤coef*(w+1)^exp) (mapSize : maps≤coef*(w+1)^exp)
      (source : ℕ→Bool) (input origin out : Memory (64*w)),
      let W:=64*w
      let depth:=(k+1)+w/2
      let grid:=TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words depth
      let off:=1+(depth+depth)
      let a:=TraceSeedWriter.archive B w (k+1) off grid.cells cap static
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let split : k+1=P.charge+rem := by dsimp only [P,rem];rw [B.charge_repeat];omega
      let X:=B.cursorState hk (w/2) off grid.cells
      let Y : State (2^B.exponent 0) (P.charge+rem):=split ▸ X
      let ss:=P.directory rem (k+1)
      let last:=TraceRecovery.lastLayer a.K ss a.cursor a.seedLayer
      let r:=Physical.nativeRun B hk machine fit hF st (s w) reps
      let C:=(Physical.registerOnLanes B (Fin size→Bool) (s w) rem X split).2
      let O:=a.cursorSeedSites B hk (w/2) off grid.cells rfl rfl
      let start:=TraceReceiverSeedWords.start machine fit hF st B hk
      let pairs:=TraceReceiverSeedWords.pairs machine fit hF st
      let desc:=TraceSourceOwner.shape W pc regs words size fuel depth grid.internal
      let trace:=TraceBitHeader.seedTraceWork (w/2) desc.stride grid.cells B.cursorCopies depth
      let unit:=FactorWork.archiveTariff w dep setup maps P.length B.localCoefficient
      let node:=traceArchive w (2^(k+1)) (2^(w/2)) ((size+1)/2) trace unit
        (directoryCap B) (directoryCap B) (directoryCap B)
      let p:=Resources.gridRows w (2^(k+1)) last.count dirs (2^(w/2)) band size node.banks.charges last.first
      let hdr:=a.control+64
      let dst:=14*2^(32*w)
      let D:=traceLimit w+ss.length*p.lanes
      ∀ enough : B.repeatFactor*(X.maxWidth+1)*B.widthBase^(s w)<2^W,
        let inner:=B.recordTable B.alphabetCap W (s w) rem Y le_rfl
          (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact enough)
        let table:=physicalTable B hk (w/2) off grid.cells (s w) W reps enough
        Post a P rem Y inner.records (2^w) (2^(3*w/5)) source input origin out →
        ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O)
          (count : Fintype.card (r.plan.finish h).Site=p.roots),
          r.plan.read table.codes (List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val))=some (h,suffix) ∧
          r.FinalNumbered h C O path ∧
          let idx:=Resources.indexEquiv r h count
          let dest:=fun j=>idx (r.plan.destination h (initialLane (Nat.succ_pos k) j))
          let work:=fun v=>unit*r.chargeAt h C start (idx.symm v)
          (Resources.registerNodes W (compactControl w) hdr (traceLimit w) a.cursor.header ss.length
            dst node O.layer p).Spec (·=out)
            (fun _ after=>Resources.Registered D dst p dest work after ∧
              (∀ z, z<a.seed → (z<dst ∨ dst+Resources.resourceLength p≤z) → after z=input z) ∧
              ∃ saved : Memory W, O.Charged node.banks (natural saved) start pairs ∧
                r.ArchiveRowsStored node.banks (natural saved) h C O path ∧
                (∀ z,p.charges≤z → z<traceLimit w → after z=saved z) ∧
                (∀ z,a.seed≤z → z<hdr → after z=out z) ∧
                TraceRecovery.stagePost a.K ss a.cursor a.seedLayer (·<hdr) (natural out)
                  (directoryCap B) (directoryCap B) (fun _=>False)
                  (r.archiveList h C O path a.seedData) (r.finalArchive h C O path).1 ∧
                MountedAt (natural out) a.K ss a.cursor) (2*2^(3*w/5)) := by
  filter_upwards [register_post_using B scale coef exp] with w applyRule
  intro pc regs words k size base fuel hk axis hp hr hs machine fit hF st reps cap static dirs band
    dep setup maps directions bandWidth externalPairs depSize setupSize mapSize source input origin out
    W depth grid off a P rem split X Y ss last r C O start pairs desc trace unit node p hdr dst D enough inner table post
  have call:=applyRule hk axis hp hr hs machine fit hF st reps cap static dirs band dep setup maps directions
    bandWidth externalPairs depSize setupSize mapSize source input origin out enough (fun _ _ _=>True)
  have choose (mid : Memory W) :
      let raw:=List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val)
      a.TraceJournal (2^w) (a.control:Word W) ((a.control+1:ℕ):Word W) P rem Y a.cursor raw origin mid →
      RecoveryRoom w a ss (directoryCap B) origin →
      ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O),
        r.plan.read table.codes raw=some (h,suffix) ∧ r.FinalNumbered h C O path ∧
        TraceRecovery.stagePost a.K ss a.cursor a.seedLayer (·<(finish a.K ss a.cursor).heap) (natural mid)
          (directoryCap B) (directoryCap B) (fun _=>False) (r.archiveList h C O path a.seedData)
          (r.finalArchive h C O path).1 ∧ True := by
    intro raw journal z
    obtain ⟨h,suffix,path,decoded,numbered,seen⟩:=repeated_recovery B hk reps a rfl rfl rfl enough (Fin size→Bool)
      (a.control:Word W) ((a.control+1:ℕ):Word W) raw origin mid journal (TraceRetainedRoom.native z.large)
      (by have:=z.large;dsimp only [W];omega) z.counters z.reads z.footprint z.halves
      z.seedStart z.seedEnd z.curRoom z.headRoom z.nodeRoom
    exact ⟨h,suffix,path,decoded,numbered,seen,trivial⟩
  obtain ⟨h,suffix,path,count,decoded,numbered,_,native⟩:=call choose post
  exact ⟨h,suffix,path,count,decoded,numbered,native⟩

end
end Hierarchy.GridPhysicalAdmission

end OAI
