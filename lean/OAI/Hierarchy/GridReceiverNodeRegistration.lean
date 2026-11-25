import OAI.ThreeFlat.Diagonal.TraceNodePublish
import OAI.Hierarchy.GridReceiverHistoryRecovery
import OAI.Hierarchy.TraceResourceGridScale

namespace OAI
/-! # Publishing and scheduling the receiver's selected roots from its own input -/
namespace Hierarchy.GridPhysicalAdmission
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution TraceAdmission TraceNodeHeaders NodePublication Filter
open scoped Classical Topology Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)

/-- Native compaction and the subsequent registration retain the sparse source words
and produce the complete chronological node directory in the saved memory. -/
structure ReceiverCache {W : ℕ} (v directory stages budget stop : ℕ) (node : NodeArchive) (old : Layer)
    (xs : List NodeRow) (mid out saved after : Memory W) : Prop where
  run : RunBounds W node (records xs) budget
  tape : TapeBounds W node (records xs)
  banks : BankInterval node (records xs) (TickWorkspace.base v 41) (TickWorkspace.base v 45)
  source : SourceRows node (NodePublication.program xs) (Resources.mounted (TickWorkspace.base v 41)
    (Resources.nodeWords (TickWorkspace.base v 41) node stages directory old) out)
  state_eq : saved=state node (NodePublication.program xs) (Resources.mounted (TickWorkspace.base v 41)
    (Resources.nodeWords (TickWorkspace.base v 41) node stages directory old) out) (records xs).length
  stage_cells : ∀ z,z<stop → after z=mid z
  seed_cells : ∀ z,TickWorkspace.base v 49≤z → z<TickWorkspace.base v 53 → after z=mid z

theorem register_receiver_post {u s : ℕ→ℕ} (scale : Scale u s) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {v pc regs words k size base fuel : ℕ}
      (lower : 4*w≤v^10) (upper : v^10≤5*w) (hk : 2≤k+1) (axis : k+1=u w+1-w/2)
      (hp : pc≤64*w) (hr : regs≤64*w) (hs : words≤64*w)
      (machine : Machine (64*w) pc regs words) (fit : NativeTrace.Fits machine size base ((k+1)+w/2) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (reps : B.blockCharge*s w≤k+1)
      (a : Archive) (place : ArchivePlacement a (TickWorkspace.base v 20) w)
      (ax : k+1=a.axes) (lanes : a.remainingLanes=2^(k+1)) (alphabet : a.K=B.alphabetCap)
      (deg : a.initialDegree=2^(B.exponent 0)) (dirs band dep setup maps : ℕ)
      (directions : dirs≤w) (bandWidth : band ≤ size) (exterior : 2*(dirs*band) ≤ size)
      (depSize : dep≤coef*(w+1)^exp) (setupSize : setup≤coef*(w+1)^exp) (mapSize : maps≤coef*(w+1)^exp)
      (source : ℕ→Bool) (input origin out : Memory (64*w)),
      let W:=64*w
      let depth:=(k+1)+w/2
      let grid:=TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words depth
      let off:=1+(depth+depth)
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let split : k+1=P.charge+rem:=by dsimp only [P,rem];rw [B.charge_repeat];omega
      let X:=B.cursorState hk (w/2) off grid.cells
      let Y:State (2^B.exponent 0) (P.charge+rem):=split ▸ X
      let ss:=P.directory rem (k+1)
      let stop:=finish a.K ss a.cursor
      let x:=a.terminal ss (P.finalEdges rem (k+1)) W
      let last:=TraceRecovery.lastLayer a.K ss a.cursor a.seedLayer
      let O:=a.cursorSeedSites B hk (w/2) off grid.cells ax lanes
      let r:=Physical.nativeRun B hk machine fit hF st (s w) reps
      let C:=(Physical.registerOnLanes B (Fin size→Bool) (s w) rem X split).2
      let start:=TraceReceiverSeedWords.start machine fit hF st B hk
      let pairs:=TraceReceiverSeedWords.pairs machine fit hF st
      let desc:=TraceSourceOwner.shape W pc regs words size fuel depth grid.internal
      let trace:=TraceBitHeader.seedTraceWork (w/2) desc.stride grid.cells B.cursorCopies depth
      let unit:=FactorWork.archiveTariff w dep setup maps P.length B.localCoefficient
      let node:=receiverArchive v (2^(k+1)) (2^(w/2)) ((size+1)/2) trace unit (directoryCap B) (directoryCap B) (directoryCap B)
      let p:=Resources.gridRows w (2^(k+1)) last.count dirs (2^(w/2)) band size node.banks.charges last.first
      let hdr:=a.control+64
      let dst:=14*2^(32*w)
      let D:=traceLimit w+ss.length*p.lanes
      a.relayWidth=2^(w/2)*(off*grid.cells*3) →
      ∀ enough : B.repeatFactor*(X.maxWidth+1)*B.widthBase^(s w)<2^W,
        let inner:=B.recordTable B.alphabetCap W (s w) rem Y le_rfl
          (by rw [State.maxWidth_cast_lanes,←Nat.mul_assoc];exact enough)
        let table:=physicalTable B hk (w/2) off grid.cells (s w) W reps enough
        Post a P rem Y inner.records (2^w) (2^(3*w/5)) source input origin out →
        ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O)
          (mid : Memory W) (count : Fintype.card (r.plan.finish h).Site=p.roots),
          r.plan.read table.codes (List.ofFn (fun j : Fin (2^(3*w/5))=>source j.val))=some (h,suffix) ∧
          r.FinalNumbered h C O path ∧ out=TerminalWireArchive.image x mid ∧
          (∀ (T : Type) (L : X.Words T),r.WordVisits (RecordedWordStep a.K (a.control:Word W) ((a.control+1:ℕ):Word W)
            stop.header stop.heap mid T B.publicTemplate) h (Physical.registerOnLanes B T (s w) rem X split).1.steps L C O path) ∧
          let idx:=Resources.indexEquiv r h count
          let dest:=fun j=>idx (r.plan.destination h (initialLane (Nat.succ_pos k) j))
          let work:=fun f=>unit*r.chargeAt h C start (idx.symm f)
          (Resources.registerNodes W (TickWorkspace.base v 41) hdr (traceLimit w) a.cursor.header ss.length dst node O.layer p).Spec
            (·=out) (fun _ after=>Resources.Registered D dst p dest work after ∧
              (∀ z,z<a.seed → after z=input z) ∧
              (∀ z,z<hdr → after z=out z) ∧
              ∃ saved : Memory W,O.Charged node.banks (natural saved) start pairs ∧
                r.ArchiveRowsStored node.banks (natural saved) h C O path ∧
                (∀ z,TickWorkspace.base v 43≤z → z<TickWorkspace.base v 45 → after z=saved z) ∧
                TraceRecovery.stagePost a.K ss a.cursor O.layer (·<hdr) (natural out)
                  (directoryCap B) (directoryCap B) (fun _=>False)
                  (r.archiveList h C O path a.seedData) (r.finalArchive h C O path).1 ∧
                MountedAt (natural out) a.K ss a.cursor ∧
                (∀ z,a.initialRecords≤z → z<a.metadataEnd → mid z=origin z) ∧
                ReceiverCache v a.cursor.header ss.length (rowBudget W node ((k+1)*2^(k+1))) stop.heap
                  node O.layer (r.archiveList h C O path a.seedData) mid out saved after) (2*2^(3*w/5)) := by
  have ur := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  have sr := (tendsto_order.mp scale.blocks).2 1 (by norm_num)
  filter_upwards [receiver_history B scale,eventual_receiver_node_admission B scale,
    eventual_native_archive_fits B scale coef exp,Resources.eventual_grid_layout scale (B.levels+1),
    eventual_native_port_count (F:=F) scale,TraceSeedWriter.eventual_fits B scale (3*5*10^26*65^14) 15,
    TraceAdmission.terminal_edges B scale,ur,sr,eventually_ge_atTop (Fintype.card F+7)] with w recover admitted fitsRows layout ports seedFit terminalEdges uNear sNear wr
  intro v pc regs words k size base fuel lower upper hk axis hp hr hs machine fit hF st reps a place ax lanes alphabet deg
    dirs band dep setup maps directions bandWidth exterior depSize setupSize mapSize source input origin out
    W depth grid off P rem split X Y ss stop x last O r C start pairs desc trace unit node p hdr dst D wire enough inner table post
  obtain ⟨h,suffix,path,mid,decoded,num,image,vis,seen,mounted,stageEnd,heapEnd,seedFrame,original⟩:=
    recover lower upper hk axis machine fit hF st reps a place ax lanes alphabet deg source input origin out enough post
  have cardinal:=Resources.final_layer_count r h C O path last seen.2.1
  refine ⟨h,suffix,path,mid,cardinal,decoded,num,image,vis,?_⟩
  intro idx dest work
  have hw : 7≤w := by omega
  have pos : (0:ℝ)<w := by exact_mod_cast (by omega : 0<w)
  have uBound : u w≤2*w := by exact_mod_cast ((div_lt_iff₀ pos).mp uNear).le
  have sBound : s w≤w := by exact_mod_cast (by simpa using ((div_lt_iff₀ pos).mp sNear).le : (s w:ℝ)≤w)
  obtain ⟨head,stage40,smallTop⟩:=receiver_areas hw lower upper
  have unitSmall : traceUnit w≤TickWorkspace.stride v :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega : w≤v^10)) 4
  have order40 : TickWorkspace.base v 40≤TickWorkspace.base v 41 := Nat.mul_le_mul_right _ (by decide)
  have order45 : TickWorkspace.base v 41≤TickWorkspace.base v 45 := Nat.mul_le_mul_right _ (by decide)
  have low : hdr+22≤TickWorkspace.base v 40 := by
    change a.control+64+22≤_;rw [place.control];change _+6*traceUnit w+64+22≤_;omega
  have fitWord : TickWorkspace.base v 20+8*(2^w)^4<2^W := by
    have cap : TickWorkspace.base v 20+8*traceUnit w≤TickWorkspace.base v 45 := by
      change 21*TickWorkspace.stride v+8*traceUnit w≤46*TickWorkspace.stride v
      omega
    exact cap.trans_lt (smallTop.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [W];omega)))
  have words0:=seedFit a _ (P.finalEdges rem (k+1)) k off grid.cells reps axis deg.symm ax lanes wire
    (ports hp hr hs axis machine fit hF st) alphabet place fitWord
  have seedWords:=TraceSeedWriter.layer_words words0 place.node ax lanes
  have old:=seen.transfer (protected':=(·<TickWorkspace.base v 40)) (mem':=natural out)
    (fun _ _=>rfl) (fun _ hz=>by omega)
  obtain ⟨rBounds,tape,scan,bank,_,chargeEnd0,time⟩:=admitted (by omega : 3*w≤v^10) upper machine fit axis hk le_rfl
    reps a place seedWords trace unit (directoryCap B) (directoryCap B) out _ _ old mounted
  have hi : TickWorkspace.base v 45≤traceLimit w := by
    have h:=(smallTop.le.trans (Nat.le_mul_of_pos_left (2^(32*w)) (by decide : 0<16)))
    exact h.trans (Nat.le_add_right ..)
  have chargeEnd : p.charges+2*(last.first+last.count)≤traceLimit w := by
    rw [seen.2.1] at chargeEnd0
    exact chargeEnd0.trans hi
  have bankFull : BankInterval node (records (r.archiveList h C O path a.seedData)) (TickWorkspace.base v 41) (traceLimit w) :=
    ⟨⟨bank.counter.1,bank.counter.2.trans_le hi⟩,⟨bank.current.1,bank.current.2.trans_le hi⟩,
      ⟨bank.header.1,bank.header.2.trans hi⟩,bank.charges,bank.nodes,
      fun j=>(bank.chargeEnd j).trans hi,fun j=>(bank.nodeEnd j).trans hi⟩
  have initial:=TraceReceiverSeedWords.seedRows machine fit hF st B hk a ax lanes deg.symm wire node.banks rfl rfl rfl rfl
  have lengthBound : k+1+w/2≤64*w := by omega
  have covered:=fitsRows machine fit hF st hk rem split le_rfl (by omega) hp hr hs lengthBound
    (by omega) (by omega) sBound h dep setup maps depSize setupSize mapSize
  obtain ⟨q,hit,actual⟩:=TraceRecovery.lastLayer_mem a.K ss a.cursor a.seedLayer
  have roots : last.count≤(k+1)*2^(k+1) := by
    have bounded:=program_site_count P a.K rem (k+1) a.cursor a.seedLayer
      (by rw [←split,seedWords.count]) q hit
    change (TraceRecovery.lastLayer a.K ss a.cursor a.seedLayer).count≤(k+1)*2^(k+1)
    simpa only [←split,actual] using bounded
  have slen : ss.length=(B.levels+1)*(s w) := (P.directory_length rem (k+1)).trans (Physical.repeated_stages B (s w))
  have full : size≤p.lanes*(2*p.pairSpan) := by
    change size≤2^(k+1)*(2*2^(w/2))
    rw [show 2^(k+1)*(2*2^(w/2))=2^(1+((k+1)+w/2)) by rw [pow_add,pow_add];ring]
    exact (Nat.le_add_right ..).trans fit.grid
  have bandRoom : p.directions*p.band≤p.lanes*p.pairSpan := by
    change dirs*band≤2^(k+1)*2^(w/2)
    change size≤2^(k+1)*(2*2^(w/2)) at full
    rw [show 2^(k+1)*(2*2^(w/2))=2*(2^(k+1)*2^(w/2)) by ring] at full
    omega
  have sz : size≤2^(32*w) := (Nat.le_add_right ..).trans (fit.grid.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have headerGap : TickWorkspace.base v 40+44≤TickWorkspace.base v 45 := by
    have h:=(trace_sector (w:=w) (by omega)).1.trans unitSmall
    change 41*TickWorkspace.stride v+44≤46*TickWorkspace.stride v
    omega
  have stageHeader : a.cursor.header+64*ss.length ≤ hdr := stageEnd
  have layoutDirectory : a.cursor.header+44+64*ss.length ≤ traceLimit w := by
    calc
      a.cursor.header+44+64*ss.length = (a.cursor.header+64*ss.length)+44 := by ac_rfl
      _ ≤ hdr+44 := Nat.add_le_add_right stageHeader 44
      _ ≤ TickWorkspace.base v 40+44 := Nat.add_le_add_right ((Nat.le_add_right hdr 22).trans low) 44
      _ ≤ traceLimit w := headerGap.trans hi
  obtain ⟨parents,linked,rows,price,target⟩:=layout (k+1) last.count dirs ss.length (2^(w/2)) band size
    node.banks.charges last.first hdr a.cursor.header axis (by omega) roots directions
    (by rw [slen];apply Nat.mul_le_mul_left;omega) (Nat.pow_le_pow_right (by decide) (by omega))
    bandWidth sz chargeEnd (low.trans (order40.trans (order45.trans hi)))
    layoutDirectory
  have seeds (j : Fin p.lanes) : (O.ord (initialLane (Nat.succ_pos k) j)).val=j.val :=
    (a.cursor_zero B hk (w/2) off grid.cells ax lanes ((CompressorPacking.Native.tagOrdinal (k+1)).symm j)).trans
      (congrArg Fin.val ((CompressorPacking.Native.tagOrdinal (k+1)).apply_symm_apply j))
  have controlFits : TickWorkspace.base v 41 ≤ 2^W :=
    order45.trans (smallTop.le.trans (Nat.pow_le_pow_right (by decide) (by omega : 32*w ≤ 64*w)))
  let savedState := NodePublication.state node (NodePublication.program (r.archiveList h C O path a.seedData))
    (Resources.mounted (TickWorkspace.base v 41)
      (Resources.nodeWords (TickWorkspace.base v 41) node ss.length a.cursor.header O.layer) out) (ss.length+1)
  have proc : (Resources.registerNodes W (TickWorkspace.base v 41) hdr (traceLimit w) a.cursor.header
      ss.length dst node O.layer p).Spec (·=out)
      (fun _ result => Resources.Registered D dst p dest work result ∧
        (∀ z, z<hdr → (z<dst ∨ dst+Resources.resourceLength p≤z) → result z=out z) ∧
        ∃ saved : Memory W, saved=savedState ∧ O.Charged node.banks (natural saved) start pairs ∧
          r.ArchiveRowsStored node.banks (natural saved) h C O path ∧
          ∀ z, p.charges≤z → z<traceLimit w → (z<dst ∨ dst+Resources.resourceLength p≤z) →
            result z=saved z)
      (43+(compactTicks (TickWorkspace.base v 41) (ss.length+1) (rowBudget W node ((k+1)*2^(k+1)))+
        Resources.registrationTicks hdr (hdr+5) ss.length p)) :=
    Resources.registerNodes_selected r h C O path a.seedData num node start pairs a.K (TickWorkspace.base v 41)
      (rowBudget W node ((k+1)*2^(k+1))) (TickWorkspace.base v 41) hdr (traceLimit w) dst (directoryCap B)
      (directoryCap B) ss a.cursor out p cardinal (initialLane (Nat.succ_pos k)) seeds seen scan
      (by omega) mounted (successors_live P rem (k+1) (by omega)) bankFull controlFits
      le_rfl le_rfl rfl initial covered rBounds tape parents linked rows (low.trans order40) stageEnd rfl rfl chargeEnd
      (target.trans (Nat.le_add_right ..)) full bandRoom
  have len : (records (r.archiveList h C O path a.seedData)).length=ss.length+1 := by
    change (TraceRecovery.records (r.archiveList h C O path a.seedData)).length=ss.length+1
    rw [seen.1,nodeLayers_length]
  rw [len] at time
  change 43+compactTicks (TickWorkspace.base v 41) (ss.length+1) (rowBudget W node ((k+1)*2^(k+1))) ≤ 2^(3*w/5) at time
  change Resources.registrationTicks hdr (hdr+5) ss.length p ≤ 2^(3*w/5) at price
  intro labels regs slots
  refine Procedure.Spec.mono (A:=Resources.registerNodes W (TickWorkspace.base v 41) hdr (traceLimit w)
    a.cursor.header ss.length dst node O.layer p) proc (fun _ e=>e) ?_ (by
      simpa only [Nat.add_assoc,two_mul] using (Nat.add_le_add time price))
  intro _ after published
  have mat := published.1
  have fr := published.2.1
  let saved : Memory W := Classical.choose published.2.2
  have registration := Classical.choose_spec published.2.2
  have snapshot := registration.1
  have funded := registration.2.1
  have written := registration.2.2.1
  have stored := registration.2.2.2
  have dstAbove : TickWorkspace.base v 45<dst := smallTop.trans_le (Nat.le_mul_of_pos_left _ (by decide : 0<14))
  have forward (z : ℕ) (lowZ : z<hdr) : after z=out z :=
    fr z lowZ (.inl (by omega))
  refine ⟨mat,fun z hz=>(forward z (by rw [show hdr=a.control+64 from rfl,place.control];rw [place.seed] at hz;omega)).trans (original z hz),
    forward,saved,funded,written,?_,seen,mounted,seedFrame,?_⟩
  · intro z first final
    exact stored z first (final.trans_le hi) (.inl (final.trans dstAbove))
  · let xs:=r.archiveList h C O path a.seedData
    let marks:=Resources.nodeWords (TickWorkspace.base v 41) node ss.length a.cursor.header O.layer
    let prior:=Resources.mounted (TickWorkspace.base v 41) marks out
    have markLength : marks.length=14 := by simp [marks,Resources.nodeWords]
    have word : TickWorkspace.base v 45<2^W := smallTop.trans_le
      (Nat.pow_le_pow_right (by decide) (by dsimp [W];omega))
    have below45 : TickWorkspace.base v 41+14≤TickWorkspace.base v 45 := by
      have h:=(trace_sector (w:=w) (by omega)).1.trans unitSmall; unfold TickWorkspace.base;omega
    have markFits : TickWorkspace.base v 41+marks.length≤2^W := by rw [markLength];omega
    have priorLow (z : ℕ) (hz : z<hdr) : prior z=out z :=
      Resources.mounted_frame _ _ _ markFits (.inl (by omega))
    have wide:=seen.transfer (protected':=(·<TickWorkspace.base v 41)) (mem':=natural prior)
      (fun z hz=>congrArg Fin.val (priorLow z hz)) (fun z hz=>by omega)
    have sources:=sourceRows_of_stagePost r h C O path a.seedData node prior ss a.cursor
      (r.finalArchive h C O path).1 wide bank (order45.trans word.le) le_rfl le_rfl rfl
    have snapshot' : saved=state node (NodePublication.program xs) prior (records xs).length := by rw [len];exact snapshot
    refine ⟨rBounds,tape,bank,sources,snapshot',?_,?_⟩
    · intro z hz
      have same : out z=mid z := by
        rw [image]
        change (if x.prefixBase ≤ z ∧ z < x.prefixBase + (x.edges+1)
          then TerminalWireArchive.prefix x mid z else mid z) = mid z
        exact ite_eq_right (fun inside => (show z < x.prefixBase from hz).not_ge inside.1)
      exact (forward z (hz.trans_le heapEnd)).trans same
    · intro z first final
      have strideUpper : TickWorkspace.base v 53<2^(32*w) := calc
        _ ≤ 2^6*TickWorkspace.stride v := Nat.mul_le_mul_right _ (by decide)
        _ = 2^(6+v^10*4) := by simp only [TickWorkspace.stride,pow_add,pow_mul]
        _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
      have addr : TickWorkspace.base v 45≤z := (Nat.mul_le_mul_right (TickWorkspace.stride v) (by decide : 46≤50)).trans first
      have old:=stored z ((Nat.mul_le_mul_right (TickWorkspace.stride v) (by decide : 44≤50)).trans first)
        (final.trans_le (strideUpper.le.trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans (Nat.le_add_right ..))))
        (.inl (final.trans (strideUpper.trans_le (Nat.le_mul_of_pos_left _ (by decide : 0<14)))))
      have eqSaved : saved z=prior z := by rw [snapshot'];exact final_stable node (NodePublication.program xs) prior rBounds (bank.stable_outside (.inr addr))
      have eqPrior : prior z=out z := Resources.mounted_frame _ _ _ markFits (.inr (by omega))
      have edgeLimit : P.finalEdges rem (k+1) ≤ 2^(3*w/5) := terminalEdges (k+1) axis reps
      have size : 2^(3*w/5)≤traceUnit w := by change _≤(2^w)^4;rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
      have far : x.prefixBase+(x.edges+1)≤z := by
        change stop.heap+(P.finalEdges rem (k+1)+1)≤z
        have heapLimit : stop.heap ≤ hdr := heapEnd
        have hd : hdr=TickWorkspace.base v 20+6*traceUnit w+64 := by rw [show hdr=a.control+64 from rfl,place.control];rfl
        have start : TickWorkspace.base v 40 ≤ z :=
          (Nat.mul_le_mul_right (TickWorkspace.stride v) (by decide : 41 ≤ 50)).trans first
        calc
          _ ≤ hdr+(traceUnit w+1) := Nat.add_le_add heapLimit (Nat.add_le_add_right (edgeLimit.trans size) 1)
          _ ≤ TickWorkspace.base v 20+7*traceUnit w+128 := by rw [hd]; omega
          _ ≤ TickWorkspace.base v 40 := stage40
          _ ≤ z := start
      have eqTerminal : out z=mid z := by
        rw [image]
        change (if x.prefixBase ≤ z ∧ z < x.prefixBase + (x.edges+1)
          then TerminalWireArchive.prefix x mid z else mid z) = mid z
        exact ite_eq_right (fun inside => far.not_gt inside.2)
      exact old.trans (eqSaved.trans (eqPrior.trans eqTerminal))

end
end Hierarchy.GridPhysicalAdmission

end OAI
