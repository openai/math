import OAI.Hierarchy.ProbeFixedWideEarnedInstall
import OAI.Hierarchy.TaggedWireEarnedStock
import OAI.Hierarchy.TaggedWireElectedSource
import OAI.Hierarchy.ProbeFixedWideBallotRead
import OAI.Hierarchy.ProbeFixedWidePaidRows

namespace OAI
/-! # Recover the installed source of each original affirmative candidate from its chronological directory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage Native CoreBoard Strip
open StripChart PurchaseStage RepairHistogram WireTelescope WideCPU StockCommit StockBound
open BoughtSockets ReportSockets CatalystArchive CatalogueRows StripDirectory PurchaseFrozen
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "W" => wordBits h D copies
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "fs" => v.nativeFormats P h width
local notation "g" => v.stamp P h width r banks src tab dst owners
local notation "st" => v.stage P h width r banks src tab dst owners
local notation "b" => v.ballot P h width r banks src tab dst owners
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
local notation "order" => v.wideOrder h width
local notation "site" => v.located (v.seed P h width) P width
variable (π : Equiv.Perm (Fin (2^h))) (m : Memory (Native.wordBits h (2^v.W) Native.copies)) (a : Attempt)
    (prior tail : List Event) (entry : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "co" => checkedOut C ((A).endAddress v.mesh) m
local notation "days" => v.birthMarks P h width r banks src tab dst owners m
local notation "ends" => (P).catalogue.physicalEnds (π:=π) (marks:=days) (P).routes.directory order rfl
local notation "elected" => (enabledBatch ((C).layout a) (repair C a)).selected (HistogramShelf.snapshot C a entry)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
set_option cleanup.letToHave false in
def wide_elected_source (slot : Slot C m (.attempt a) prior tail entry)
    (boot : CoreRoute.Seen order v.radius groups packed socket v.depth π m) («public» : (E).Resident m)
    (mounted : Calendar.mounted C (events v.mesh) m) (room : (A).endAddress v.mesh<2^W)
    (stored : ArchiveRoom C m (v.mesh.inject+v.mesh.cool)) (late : v.stripHeight≤h) (small : width≤2^h)
    (limit : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h) (catRoom : (P).catalogue.rows<2^W)
    (cols : Fintype.card (Columns h D)≤2^W) (stages : Stages h D≤2^W) (degree : v.sampler.degree≤2^W)
    (layout : TrialLayout C a (fs a).pricedArea (fs a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (i : Fin ((C).layout a).candidates) (picked : committed (enabledBatch ((C).layout a) (repair C a)) (HistogramShelf.snapshot C a entry) (i.val:Word W)) :
    v.ElectedSource h width π days ends co a i.val := by
  have occurs : Event.attempt a ∈ events v.mesh := by
    change Event.attempt a ∈ events (C).mesh
    rw [slot.events]
    simp
  have fits:=v.market_rows_fit P h width late a
  let L:=(C).layout a
  let B:=repair C a
  have before:=v.ballot_before P h width r banks src tab dst owners a
  have wide:=layout.window.wide
  have equal:=priced_liveRows L B (fs a).pricedArea (fs a).stockSource (g a) (prepared C a entry)
    slot.currentReady.2.2.2.2.2.2.1 slot.currentReady.2.2.2.2.2.2.2.1 (by omega)
    before (before.trans (Nat.le_succ _)) layout.window.label
  let liveAt (mem : Memory W) : Prop :=
    i ∈ StockCommit.liveRows (b a) (st a mem) (fs a).market.rows
  have live : liveAt entry := by
    have selected : i ∈ StockCommit.liveRows (enabledBatch L B)
        (postSnapshot L B (prepared C a entry)) L.candidates :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, picked⟩
    exact (congrArg (fun rows : Finset (Fin L.candidates) => i ∈ rows) equal).mpr selected
  have checked:=v.wide_paid_checkout_reads h width r banks src tab dst owners π m ((A).endAddress v.mesh)
    boot «public» room mounted le_rfl
  cases a with
  | outer phase trial =>
    let ev:=Attempt.outer phase trial
    have mask:=v.catalyst_date_mask P h width r banks src tab dst owners m ev mounted occurs
      (v.catalystMaskBounds_at_height P h width r banks src tab dst owners limit ev)
    have observed := mask.live (fs ev).stockSource i
    have atEntry : CatalystArchive.entryMemory C m ev = entry := slot.entryMemory
    have actual := observed ((congrArg liveAt atEntry).mpr live)
    rw [atEntry] at actual
    have initial:=v.payload_live_lt P h width phase trial ((guard C ev).apply entry) i (i.isLt.trans_le fits)
      actual
    let root : Fin (2^h):=⟨i.val,initial⟩
    let ports := v.payloadPricePorts P h width
    let extra := LocalCommodity.extraEnds (PayloadStrip.commodity (Stages h D) k)
      (PayloadStrip.noProbe (Stages h D))
    let col := payloadPlace (d:=D) π root
    let unused := (P).catalogue.coreIndex
      ((v.wideOrder h width).symm (.inl (.inl (.inl root, ⟨0,v.positive⟩, false))))
    obtain ⟨column,roads⟩ := v.payload_row_placement_of_fields P h width π groups packed rfl order co
      (checked.base.board ev).columns (checked.base.board ev).input checked.base.loaded cols root
      (v.date_prefix_fit h).le
    let install : EarnedInstall (sam:=v.sampler) (h:=h) (d:=D) (k:=k)
        (n:=PayloadStrip.edgeCount (Stages h D)) (K:=siteLast h D k+1) (w:=W)
        («A»:=PayloadStrip.Quotes (Stages h D) k) (B:=Empty) (Ball:=Fin (2^h))
        ports (P).catalogue π extra (SiteDirectory.payloadParties (d:=D) (k:=k) π)
        root ends (siteNumber h D k).toEmbedding (PayloadStrip.rowAddress root) co (root.val:Word W) := {
      lookup := order
      loaded := checked.base.loaded
      wide := catRoom
      col := col
      placed := by
        refine ⟨column,ports.earned_geometry (P).catalogue order co (root.val:Word W)
          checked.base.loaded catRoom π col extra column ends
          (fun f => (P).catalogue.physicalEnds_core (π:=π) (marks:=days) (P).routes.directory order rfl f)
          ?_ (fun j => j.elim) unused⟩
        intro edge lane
        obtain ⟨f,word,_,faces⟩ := roads edge lane
        exact ⟨f,word,faces⟩
      core := (P).catalogue.physicalEnds_core (π:=π) (marks:=days) (P).routes.directory order rfl
      mapped := fun _ => rfl
      goods := earned_payload_goods (h:=h) (d:=D) (k:=k) π root
    }
    exact .payload phase trial root i.val rfl install (fun j => StripDirectory.payloadSlot_read co root j)
  | inner ph tr sj ti =>
    let ev:=Attempt.inner ph tr sj ti
    obtain ⟨hp,ht,hj,hi⟩:=scheduled_inner v.mesh ph tr sj ti occurs
    let p : Fin (v.mesh.inject+v.mesh.cool):=⟨ph,hp⟩
    let t : Fin v.mesh.outerFuel:=⟨tr,ht⟩
    let j : Fin v.mesh.reserveSteps:=⟨sj,hj⟩
    let n : Fin v.mesh.innerFuel:=⟨ti,hi⟩
    have entryEq : CatalystArchive.entryMemory C m ev = entry := slot.entryMemory
    have belongs := v.wide_paid_paths h width r banks src tab dst owners π m p t j n boot «public» room
      mounted late small limit layout stored i ((congrArg liveAt entryEq).mpr live)
    let path:=belongs.choose
    have pos : (BoughtLocation.relative path).val=i.val:=congrArg Fin.val belongs.choose_spec
    let u:=v.paid_days_exclusive h width r banks src tab dst owners m
    have bounds:=v.purchased_table_room h late
    let bornDay := finProdFinEquiv (p,t)
    let register : Word W := (BoughtLocation.relative path).val
    let ports := v.purchasedPricePorts P h width p t
    let extra := LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth)
    let bought : ReportSockets.Bought v.sampler π v.depth days := ⟨bornDay,path⟩
    have capacity : ((P).routes.directory.header h D k v.sampler.degree v.depth).count =
        (P).catalogue.boughtRows := rfl
    let relative := Fin.cast capacity (((P).routes.directory.header h D k v.sampler.degree v.depth).enum
      ⟨bornDay,BoughtLocation.relative path⟩)
    have records := checked.ports p t (BoughtLocation.keyOf path)
    have placement := v.purchased_row_placement_of_fields P h width π groups packed rfl rfl order co
      p t (checked.base.board ev).columns (checked.base.board ev).strata checked.base.loaded cols
      (days bornDay) (u bornDay) path records bounds.1 bounds.2.1 stages degree
      (v.date_prefix_fit h).le capacity.le catRoom
    obtain ⟨column,roads,_⟩ := placement
    refine pos ▸ ElectedSource.purchased ph tr sj ti hp ht u path (BoughtLocation.relative path).val rfl ?_ ?_
    · refine {
        lookup := order
        loaded := checked.base.loaded
        wide := catRoom
        col := retainedCol π (days bornDay) path
        placed := ?_
        core := (P).catalogue.physicalEnds_core (π:=π) (marks:=days) (P).routes.directory order capacity
        mapped := fun x => congrArg
          (fun y : ColumnSite (StageColumns h D) k => siteNumber h D k (stageSitesIntoPayload k y))
          (allTreeSites_single v.sampler π v.depth (days bornDay) (u bornDay) path x)
        goods := earned_purchase_goods (h:=h) (d:=D) (k:=k) π v.sampler v.depth (days bornDay) path }
      refine ⟨column,ports.earned_geometry (P).catalogue order co register checked.base.loaded catRoom π
        (retainedCol π (days bornDay) path) extra column ends
        (fun f => (P).catalogue.physicalEnds_core (π:=π) (marks:=days) (P).routes.directory order capacity f)
        ?_ ?_ ((P).catalogue.boughtIndex relative)⟩
      · intro e l
        obtain ⟨f,read,_,faces⟩ := roads e l
        exact ⟨f,read,faces⟩
      · intro probe
        cases probe
        obtain ⟨word,faces⟩ := original_faces (P).catalogue (P).routes.directory capacity bought co register .row rfl
        refine ⟨relative,word,?_⟩
        change Faces _ _ (ends (((P).catalogue.ordinal v.sampler π v.depth days order capacity) (.inr bought)))
        rw [(P).catalogue.physicalEnds_at (P).routes.directory order capacity (.inr bought)]
        exact faces
    · intro axis
      exact relative_stock_at (((v.nativeBoards P h width).outer p t).market.shelf)
        ((v.nativeBoards P h width).stratumHeader p t) (days bornDay) path co
        records.tiles (checked.base.board ev).strata bounds.1 bounds.2.1 axis

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
