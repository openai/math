import OAI.Hierarchy.ProbeFixedForestBandwidth
import OAI.Hierarchy.ProbeFixedWidePaidRows
import OAI.Hierarchy.ProbeFixedModeLifetimes
import OAI.Hierarchy.ProbeFixedForestTariffs
import OAI.Hierarchy.ProbeFixedForestCommitted
import OAI.Hierarchy.ProbeFixedWideForestBase
import OAI.Hierarchy.ProbeFixedWidePurchasedRows
import OAI.Hierarchy.ProbeFixedPaidPortData
import OAI.Hierarchy.ProbeFixedWideBroadcastBits
import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProtocolRAMCatalystStripDates

namespace OAI
/-! # Uniform per-reporter forest bandwidth on both original settlement memories -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT ReportSockets
open ProbeStage.Native CoreRoute CatalogueRows StockCommit StripDirectory CatalystArchive BoughtSockets PurchaseStage
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

/-- Every tree has one span per local column adjacency and two signed radii
per axis in every column. This constant uses neither height nor payload width. -/
def forestFactor :=
  let n:=max (PayloadStrip.edgeCount (publicStages v.W)) (ChainStrip.edgeCount v.depth)
  (n+(n+1)*(k*2))*v.maxBits

theorem wide_forest_aperture :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.keepLimit*width+1 ≤ 2^h →
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let stock:=v.fixedTerminalStock P h width
      let r:=Fintype.card (Slots h (2^v.W) k)
      let page:=v.wideSignedPage h width stock
      let count:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A))
      let _owners:=sinkBank (v.catalystStaticStart P h width) count r P.catalogue.rows
      let _banks:=TerminalLayout.settlement page stock
      let _src:=TerminalLayout.source page
      let _tab:=TerminalLayout.table page
      let _dst:=TerminalLayout.destination page
      ∀size,A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let m:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw
        let out:=run (v.wideSignedChart h width stock) (events v.mesh) m
        ∀a,Event.attempt a∈events v.mesh→
          let f:=v.nativeFormats P h width a
          let t:=v.nativeTrees P h width a
          let sl:=PaidWidths.paidBroadcast f.pricedArea t.positions t.owner t.parity t.edge t.sourceRow f.board.batch.copies v.maxBits
          ∀e : Fin P.catalogue.rows,sl.load out e≤v.forestFactor*width ∧
            sl.load (v.wideSignedCheckoutAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw) e≤v.forestFactor*width := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let payloadCard:=Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount (publicStages v.W)) k)
  let purchaseCard:=Fintype.card (Strip.TreeLink (ChainStrip.edgeCount v.depth) k)
  filter_upwards [v.wide_row_room,v.wide_face_room,Filter.eventually_ge_atTop v.wideStockHeight,
    Filter.eventually_ge_atTop ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊,
    Filter.eventually_ge_atTop (max payloadCard purchaseCard),Filter.eventually_ge_atTop v.maxBits] with h rowRoom faceRoom tall cutRoom treeRoom bits
  intro width small budget P A stock size extent π raw m out a occurs fmt forest sl edge
  let r:=Fintype.card (Slots h (2^v.W) k)
  let page:=v.wideSignedPage h width stock
  let count:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A))
  let _owners:=sinkBank (v.catalystStaticStart P h width) count r P.catalogue.rows
  let _banks:=TerminalLayout.settlement page stock
  let _src:=TerminalLayout.source page
  let _tab:=TerminalLayout.table page
  let _dst:=TerminalLayout.destination page
  let chart:=v.wideSignedChart h width stock
  let S:=v.nativeBoards P h width
  let site:=v.located (v.seed P h width) P width
  let ordCore:=v.wideOrder h width
  let W:=wordBits h (2^v.W) Native.copies
  let core:=P.routes.core
  let groups:=WideMemory.groups h v.W
  let packed:=WideMemory.dir h v.W k v.wideJobs
  have sizes:=v.wide_stock_sizes h width tall budget small
  have stockRun:=v.wide_stock_at h width size extent v.radius π raw tall budget small
  have whole:=stockRun.mounted_all
  obtain ⟨_,_,boot,pub,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock v.radius π
    (wideRouteOrder h (2^v.W) k) raw sizes.words.addresses
  let coreEdge : Edges v.sampler h (2^v.W) k:=
    .inl (.inl ((.inl ⟨0,by positivity⟩ : Columns h (2^v.W)),⟨0,v.positive⟩,false))
  have pos : 0<P.catalogue.coreRows:=(Nat.zero_le _).trans_lt (ordCore.symm coreEdge).isLt
  have enough : h≤2^W:=(Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le
  have pc : Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount (Stages h (2^v.W))) k)≤2^W:=by
    rw [show Stages h (2^v.W)=publicStages v.W from fixed_stage_count h v.W]
    exact ((le_max_left payloadCard purchaseCard).trans treeRoom).trans enough
  have bc : purchaseCard≤2^W:=((le_max_right payloadCard purchaseCard).trans treeRoom).trans enough
  have rows : fmt.pricedArea.rows=treeRows site v.mesh P.catalogue P.routes F a :=
    (candidate_count F v.mesh A P.joint.initial S a).trans (by cases a <;> rfl)
  have rowFits : fmt.pricedArea.rows≤2^W:=v.market_rows_fit P h width sizes.strip a
  let fin:=v.wideSignedCheckoutAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw
  have all (ev) (hit : Event.attempt ev∈events v.mesh):=(v.wide_stock_layout h width size extent v.radius π raw sizes.words
    budget sizes.width sizes.alphabet sizes.rowsMass sizes.roles ev hit).1
  have archive:=v.mode_archive P h width r _banks _src _tab _dst _owners m stockRun all
  let days:=v.birthMarks P h width r _banks _src _tab _dst _owners m
  have bounds:=v.wide_broadcast_bits h width size extent v.radius π raw tall budget small bits a occurs
  have nc : fmt.board.batch.copies≤width:=(v.ordinary_dimensions P h width a).2.le.trans (Nat.div_le_self ..)
  have full : fmt.board.batch.copies*v.maxBits<2^W :=
    (Nat.mul_le_mul_right v.maxBits (nc.trans small)).trans_lt (GlobalTests.linear_room h (2^v.W) v.maxBits bits)
  have common (ell : ℕ) (hl : ell≤ max (PayloadStrip.edgeCount (publicStages v.W)) (ChainStrip.edgeCount v.depth)) :
      (ell+(ell+1)*(k*2))*(fmt.board.batch.copies*v.maxBits)≤v.forestFactor*width := by
    dsimp [forestFactor]
    calc
      _≤(max (PayloadStrip.edgeCount (publicStages v.W)) (ChainStrip.edgeCount v.depth)+
           (max (PayloadStrip.edgeCount (publicStages v.W)) (ChainStrip.edgeCount v.depth)+1)*(k*2))*(width*v.maxBits) :=
        Nat.mul_le_mul (Nat.add_le_add hl (Nat.mul_le_mul_right _ (Nat.add_le_add_right hl _))) (Nat.mul_le_mul_right _ nc)
      _=_:=by ac_rfl
  have pass (now : Memory W) (base : v.WidePaidReadout h width r _banks _src _tab _dst _owners π m now)
      (numbers : v.BroadcastBounds h width a now)
      (same : ∀i : Fin fmt.pricedArea.rows,now (fmt.pricedArea.broadcast+i.val)=out (fmt.pricedArea.broadcast+i.val)) :
      sl.load now edge≤v.forestFactor*width := by
    obtain ⟨_,size,copySize,bounded,_⟩:=numbers
    have head : forest.Reads now (fun i : Fin fmt.pricedArea.rows=>treeWalk site v.mesh P.catalogue P.routes a now i.val pos) := by
      rw [rows]
      exact v.native_forest_resident P h width now base.base.public a occurs (rowRoom width).1 pos (rows ▸ rowFits) pc bc
    have charged (i : Fin fmt.pricedArea.rows)
        (positive : 0 < (now (fmt.pricedArea.broadcast + i.val)).val) :
        (out (fmt.pricedArea.broadcast + i.val)).val ≠ 0 := by
      intro zero
      exact (Nat.ne_of_gt positive) ((congrArg (fun word : Word W => word.val) (same i)).trans zero)
    cases a with
    | outer phase trial =>
      obtain ⟨prior,tail,split⟩:=List.append_of_mem occurs
      let entry:=run chart prior m
      have step:=slot_of_split chart m _ prior tail entry split rfl whole
      have covers (i : Fin fmt.pricedArea.rows) (yes : 0<(now (fmt.pricedArea.broadcast+i.val)).val) : i.val<2^h := by
        have active:=v.forest_candidate_live P h width r _banks _src _tab _dst _owners _ m entry prior tail step (all _ occurs)
          sizes.strip small whole cutRoom i (charged i yes)
        exact v.payload_live_lt P h width phase trial ((guard chart _).apply entry) i (i.isLt.trans_le rowFits) active
      have dated := base.base.board (Attempt.outer phase trial)
      have raw:=v.payload_forest_bandwidth_of_fields P h width π groups packed rfl ordCore now phase trial dated.columns dated.input
        base.base.loaded faceRoom.1 (v.date_prefix_fit h).le (rowRoom width).1 fmt.pricedArea edge forest pos
        fmt.board.batch.copies v.maxBits size copySize bounded full (v.date_market_rows h P width _) head covers
      apply raw.trans
      apply common
      rw [show Stages h (2^v.W)=publicStages v.W from fixed_stage_count h v.W]
      exact le_max_left ..
    | inner p t j repair =>
      obtain ⟨hp,ht,hj,hx⟩:=scheduled_inner v.mesh p t j repair occurs
      let phase : Fin (v.mesh.inject+v.mesh.cool):=⟨p,hp⟩
      let trial : Fin v.mesh.outerFuel:=⟨t,ht⟩
      let slice : Fin v.mesh.reserveSteps:=⟨j,hj⟩
      let tick : Fin v.mesh.innerFuel:=⟨repair,hx⟩
      let ev:=Attempt.inner p t j repair
      let entry:=innerState chart m phase trial slice tick
      obtain ⟨tail,step⟩:=inner_slot chart m phase trial slice tick hp ht hj hx whole
      let phaseID:=finProdFinEquiv (phase,trial)
      let marks:=days phaseID
      have unique:=v.paid_days_exclusive h width r _banks _src _tab _dst _owners m phaseID
      have cells:=v.purchased_table_room h sizes.strip
      have covers (i : Fin fmt.pricedArea.rows) (yes : 0<(now (fmt.pricedArea.broadcast+i.val)).val) :
          ∃u : LiveChains v.sampler π v.depth marks,(BoughtLocation.relative u).val=i.val := by
        have chosen:=v.forest_committed P h width r _banks _src _tab _dst _owners ev m entry _ tail step (all ev occurs)
          sizes.strip small i (charged i yes)
        have pick:=v.wide_paid_paths h width r _banks _src _tab _dst _owners π m phase trial slice tick boot pub
          sizes.words.addresses whole sizes.strip small cutRoom (all ev occurs) archive i
        let live (mem : Memory W) : Prop :=
          i ∈ StockCommit.liveRows (v.ballot P h width r _banks _src _tab _dst _owners ev)
            (v.stage P h width r _banks _src _tab _dst _owners ev mem) fmt.pricedArea.rows
        have selected : live entry := Finset.mem_filter.mpr ⟨Finset.mem_univ i, chosen⟩
        have entryEq : CatalystArchive.entryMemory chart m ev = entry := step.entryMemory
        have real := pick ((congrArg live entryEq).mpr selected)
        obtain ⟨u,eq⟩:=real
        exact ⟨u,congrArg Fin.val eq⟩
      have dated := base.base.board (Attempt.inner p t j repair)
      have raw:=v.purchased_forest_bandwidth_of_fields P h width π groups packed rfl rfl ordCore now phase trial slice tick dated.columns dated.strata
        base.base.loaded faceRoom.1 marks unique (fun u=>base.ports phase trial (BoughtLocation.keyOf u)) cells.1
        cells.2.1 faceRoom.2.1 faceRoom.2.2 (v.date_prefix_fit h).le le_rfl (rowRoom width).1 fmt.pricedArea edge forest pos
        fmt.board.batch.copies v.maxBits size copySize bounded full (candidate_count F v.mesh A P.joint.initial S ev).symm.le
        head covers
      exact raw.trans (common _ (le_max_right ..))
  apply And.intro (pass out (v.wide_paid_run_reads h width r _banks _src _tab _dst _owners π m boot pub sizes.words.addresses whole)
    bounds.1 (fun _=>rfl))
  apply pass fin (v.wide_paid_checkout_reads h width r _banks _src _tab _dst _owners π m (A.endAddress v.mesh) boot pub
    sizes.words.addresses whole le_rfl) bounds.2
  intro i
  have inside : fmt.pricedArea.broadcast+i.val<fmt.pricedArea.stop := by
    have hi:=i.isLt
    unfold StockCommit.Area.stop StockCommit.Area.output StockCommit.Area.excess StockCommit.Area.clip StockCommit.Area.src
    omega
  have earlier:=inside.trans_le ((v.attempt_room P h width a).trans (A.within v.mesh _ occurs))
  exact ProtocolRAMGeneratedWrite.frame_image _ 1 _ _ _ (.inl earlier)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
