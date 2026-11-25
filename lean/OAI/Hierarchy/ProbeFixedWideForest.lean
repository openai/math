import OAI.Hierarchy.ProbeFixedForestTariffs
import OAI.Hierarchy.ProbeFixedForestCommitted
import OAI.Hierarchy.ProbeFixedWideForestBase
import OAI.Hierarchy.ProbeFixedWidePurchasedRows
import OAI.Hierarchy.ProbeFixedPaidPortData
import OAI.Hierarchy.ProbeFixedWideAttemptInvoice
import OAI.Hierarchy.ProtocolRAMCatalystStripDates

namespace OAI
/-! # The true forest and its invoice at the final signed RAM state -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT ReportSockets
open ProbeStage.Native CoreRoute CatalogueRows StockCommit StripDirectory CatalystArchive BoughtSockets PurchaseStage
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_forest_invoice :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.keepLimit*width+1 ≤ 2^h →
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let stock:=v.fixedTerminalStock P h width
      let r:=Fintype.card (Slots h (2^v.W) k)
      let page:=v.wideSignedPage h width stock
      let count:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A))
      let owners:=sinkBank (v.catalystStaticStart P h width) count r P.catalogue.rows
      let banks:=TerminalLayout.settlement page stock
      let src:=TerminalLayout.source page
      let tab:=TerminalLayout.table page
      let dst:=TerminalLayout.destination page
      ∀size,A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let m:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw
        let out:=run (v.wideSignedChart h width stock) (events v.mesh) m
        let days:=v.birthMarks P h width r banks src tab dst owners m
        let ord:=P.catalogue.ordinal v.sampler π v.depth days (v.wideOrder h width) rfl
        let len:=extendedLength ord (lenCode v.sampler π v.depth days v.radius)
        ∀a, Event.attempt a∈events v.mesh →
          let f := v.nativeFormats P h width a
          let forest := v.nativeTrees P h width a
          ∃tree : Fin f.pricedArea.rows→List (Fin P.catalogue.rows), forest.Reads out tree ∧
            ∀i,(out (f.pricedArea.broadcast+i.val)).val≠0 → ((tree i).map len).sum≤v.cost.atAttempt a := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let payloadCard:=Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount (publicStages v.W)) k)
  let purchaseCard:=Fintype.card (Strip.TreeLink (ChainStrip.edgeCount v.depth) k)
  filter_upwards [v.wide_row_room,v.wide_face_room,Filter.eventually_ge_atTop v.wideStockHeight,
    Filter.eventually_ge_atTop ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊,
    Filter.eventually_ge_atTop (max payloadCard purchaseCard)] with h rowRoom faceRoom tall cutRoom treeRoom
  intro width small budget P A stock r page count owners banks src tab dst size extent π raw m out days ord len a occurs fmt forest
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
  have base:=v.wide_forest_run_base h width r banks src tab dst owners π m boot pub sizes.words.addresses whole
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
  let tree (i : Fin fmt.pricedArea.rows):=treeWalk site v.mesh P.catalogue P.routes a out i.val pos
  refine ⟨tree,?_,?_⟩
  · dsimp only [tree]
    rw [rows]
    exact v.native_forest_resident P h width out base.public a occurs (rowRoom width).1 pos
      (rows ▸ rowFits) pc bc
  intro i on
  have layout:=(v.wide_stock_layout h width size extent v.radius π raw sizes.words budget
    sizes.width sizes.alphabet sizes.rowsMass sizes.roles a occurs).1
  cases a with
  | outer phase trial =>
    obtain ⟨prior,tail,split⟩:=List.append_of_mem occurs
    let entry:=run chart prior m
    have step:=slot_of_split chart m _ prior tail entry split rfl whole
    have active:=v.forest_candidate_live P h width r banks src tab dst owners _ m entry prior tail step layout
      sizes.strip small whole cutRoom i on
    have real:=v.payload_live_lt P h width phase trial ((guard chart _).apply entry) i (i.isLt.trans_le rowFits) active
    let ball : Fin (2^h):=⟨i.val,real⟩
    have dated := base.board (Attempt.outer phase trial)
    exact v.payload_forest_invoice_of_fields P h width π groups packed rfl ordCore out phase trial dated.columns dated.input base.loaded faceRoom.1 ball
      (v.date_prefix_fit h).le (rowRoom width).1 days rfl pos
  | inner p t j repair =>
    obtain ⟨hp,ht,hj,hx⟩:=scheduled_inner v.mesh p t j repair occurs
    let phase : Fin (v.mesh.inject+v.mesh.cool):=⟨p,hp⟩
    let trial : Fin v.mesh.outerFuel:=⟨t,ht⟩
    let slice : Fin v.mesh.reserveSteps:=⟨j,hj⟩
    let tick : Fin v.mesh.innerFuel:=⟨repair,hx⟩
    let entry:=innerState chart m phase trial slice tick
    obtain ⟨tail,step⟩:=inner_slot chart m phase trial slice tick hp ht hj hx whole
    have active:=v.forest_candidate_live P h width r banks src tab dst owners _ m entry _ tail step layout
      sizes.strip small whole cutRoom i on
    have born:=v.wide_birth_rows h width r banks src tab dst owners π m boot whole sizes.words.addresses phase trial slice tick
    have sourcePrefix:=v.wideGeometryPrefix h width
    have first:=v.catalyst_initial_le_first P h width
    let keyPage:=Public.keyHead v.sampler P.routes.column h v.W k v.depth
    let coreEnd:=CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
      packed.groups (WideMemory.H h v.W k v.wideJobs) P.catalogue.coreRows
    have low : keyPage.stop≤A.first:=(show keyPage.stop≤coreEnd from
      (Public.borders v.sampler P.routes.column h v.W k v.wideJobs v.depth).2.trans (Nat.le_add_right ..)).trans
        (sourcePrefix.2.2.trans first)
    have geometry : PurchaseFrozen.Shelf.Geometry π m:=fun e=>⟨_,boot.board.columns.geometry e⟩
    obtain ⟨marks,unique,path,ix,_⟩:=v.purchased_post_path P h width r banks src tab dst owners m π phase trial slice tick whole
      geometry (sourcePrefix.2.1.trans first) low boot.board.rom.keys born sizes.strip i active
    have records:=v.terminal_port_data P h width r banks src tab dst owners m π phase trial whole geometry
      (sourcePrefix.2.1.trans first) low boot.board.rom.keys (BoughtLocation.keyOf path)
    have cells:=v.purchased_table_room h sizes.strip
    have dated := base.board (Attempt.inner p t j repair)
    have charge:=v.purchased_forest_invoice_of_fields P h width π groups packed rfl rfl ordCore out phase trial slice tick dated.columns dated.strata base.loaded
      faceRoom.1 marks unique path records cells.1 cells.2.1 faceRoom.2.1 faceRoom.2.2 (v.date_prefix_fit h).le
      le_rfl (rowRoom width).1 days rfl pos
    simpa only [ix] using charge

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
