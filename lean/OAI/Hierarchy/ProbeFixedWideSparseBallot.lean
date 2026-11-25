import OAI.Hierarchy.ProbeSparseParticipantSheet
import OAI.Hierarchy.ProbeFixedWideBallotRead
import OAI.Hierarchy.ProbeFixedWidePacketFields
import OAI.Hierarchy.TaggedWireEarnedSites
import OAI.Hierarchy.ProbeFixedWidePaidRows

namespace OAI
/-! # The native elected-party sheet on the original payload or acquired strip -/

noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2000000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage Native CoreBoard
open StripChart PurchaseStage RepairHistogram WireTelescope WideCPU StockCommit StockBound
open BoughtSockets ReportSockets CatalystArchive
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "S" => v.nativeBoards P h width
local notation "D" => 2^v.W
local notation "W" => wordBits h D copies
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "fs" => v.nativeFormats P h width
local notation "g" => v.stamp P h width r banks src tab dst owners
local notation "st" => v.stage P h width r banks src tab dst owners
local notation "b" => v.ballot P h width r banks src tab dst owners
local notation "sh" => v.widePacketShape h width
local notation "sz" => siteLast h D k+1
local notation "parts" => v.wideBallotParties h

/-- The actual elected row set, taken at the true stock-batch input. -/
def wideBallotRows (a : Attempt) (entry : Memory W) :=
  liveRows (b a) (st a entry) (fs a).market.rows

section Selection
variable (siteROM : ℕ) (a : Attempt) (prior tail : List Event) (m entry processing : Memory (wordBits h (2^v.W) copies))
    (cut : Slot (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners) m (.attempt a) prior tail entry)
    (preserved : ∀x,x<(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh→processing x=checkedOut (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners) ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh) m x)
    (layout : TrialLayout (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners) a (v.nativeFormats (v.widePlacement h width) h width a).pricedArea (v.nativeFormats (v.widePlacement h width) h width a).stockSource (v.stamp (v.widePlacement h width) h width r banks src tab dst owners a) v.keepLimit width
      ((v.privateArena (v.widePlacement h width) h width).base v.mesh (.attempt a)))

include cut preserved layout in
theorem wide_packet_live_row (bits : ℕ) (stride : Bank) (old new : ℕ)
    (board : PurchaseStage.Board ((C).layout a) (repair C a) W) (room : ((C).layout a).candidates≤2^W)
    (i : Fin (fs a).market.rows) (j : Fin (parts a)) :
    ((v.widePacketFields h width bits (.attempt a) siteROM stride old new).selected j).eval processing (i.val:Word W)≠0 ↔
      i∈v.wideBallotRows h width r banks src tab dst owners a entry := by
  rw [v.widePacket_selected h width bits siteROM stride old new a j,
    v.wide_ballot_live P h width r banks src tab dst owners siteROM a prior tail m entry processing cut preserved board room j i]
  let f:=fs a
  let L:=(C).layout a
  let B:=repair C a
  have before:=v.ballot_before P h width r banks src tab dst owners a
  have wide:=layout.window.wide
  have equal:=priced_liveRows L B f.pricedArea f.stockSource (g a) (prepared C a entry)
    cut.currentReady.2.2.2.2.2.2.1 cut.currentReady.2.2.2.2.2.2.2.1 (by omega) before (before.trans (Nat.le_succ _)) layout.window.label
  let idx : Fin L.candidates := ⟨i.val,i.isLt⟩
  change committed (enabledBatch L B) (postSnapshot L B (prepared C a entry)) (idx.val:Word W) ↔
    idx∈StockCommit.liveRows (enabledBatch L B) (stageInput f.pricedArea f.stockSource (g a)
    (postOutput L B (prepared C a entry))) L.candidates
  rw [equal]
  simp only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and]

end Selection

variable [Nonempty (Fin k)]
variable (π : Equiv.Perm (Fin (2^h))) (m : Memory (wordBits h (2^v.W) copies)) (a : Attempt) (prior tail : List Event) (entry processing : Memory (wordBits h (2^v.W) copies))
local notation "rows" => v.wideBallotRows h width r banks src tab dst owners a entry
local notation "co" => checkedOut C ((A).endAddress v.mesh) m
local notation "days" => v.birthMarks P h width r banks src tab dst owners m
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
local notation "order" => v.wideOrder h width
local notation "booted" => CoreRoute.Seen order v.radius groups packed socket v.depth π m

theorem wide_ballot_scattered (bits siteROM rom start old new : ℕ) (stride : Bank)
    (slot : Slot C m (.attempt a) prior tail entry)
    (boot : booted) («public» : (E).Resident m) (mounted : Calendar.mounted C (events v.mesh) m)
    (room : (A).endAddress v.mesh<2^W) (stored : ArchiveRoom C m (v.mesh.inject+v.mesh.cool))
    (late : v.stripHeight≤h) (small : width≤2^h)
    (limit : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h)
    (catRoom : (P).catalogue.rows<2^W) (cols : Fintype.card (Columns h D)≤2^W)
    (stages : Stages h D≤2^W) (degree : v.sampler.degree≤2^W)
    (layout : TrialLayout C a (fs a).pricedArea (fs a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (board : PurchaseStage.Board ((C).layout a) (repair C a) W)
    (preserved : ∀x,x<(A).endAddress v.mesh→processing x=co x)
    (sitePage : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) processing)
    (siteSize : SiteDirectory.size h D k≤2^W)
    (safe : PublicSheet (sh (.attempt a)) sz rom start W
      (v.widePacketFields h width bits (.attempt a) siteROM stride old new) processing) :
    let fields:=v.widePacketFields h width bits (.attempt a) siteROM stride old new
    let sheet:=(sh (.attempt a)).sheet sz rom start fields
    ∃party : rows×Fin (parts a) ↪ Fin sz,
      (∀u : rows×Fin (parts a),(fields.site u.2).eval processing (u.1.val.val:Word W)=((party u).val:Word W)) ∧
      ∃out,(sheet.code W).Exec processing out sheet.ticks ∧
        (∀s c,out (start+1+(SiteScatter.pos s c).val)=
          SiteScatter.table party (fun u j=>(fields.value u.2 j).eval processing (u.1.val.val:Word W)) s c) ∧
        ∀x,(x<start+1 ∨ start+1+sz*(sh (.attempt a)).columns≤x) →
          (x<start+1+sz*(sh (.attempt a)).columns ∨ start+1+sz*(sh (.attempt a)).columns+
            (sh (.attempt a)).count+(sh (.attempt a)).count≤x) → x≠start → out x=processing x := by
  intro fields sheet
  have occ : Event.attempt a∈events v.mesh:=by change _∈events (C).mesh;rw [slot.events];simp
  have fits:=(v.market_rows_fit P h width late a)
  have all:=v.wide_paid_checkout_reads h width r banks src tab dst owners π m ((A).endAddress v.mesh) boot «public» room mounted le_rfl
  have votes (i j):=(v.wide_packet_live_row h width r banks src tab dst owners siteROM a prior tail m entry processing
    slot preserved layout bits stride old new board fits i j)
  obtain ⟨party,identify⟩ : ∃party : rows×Fin (parts a) ↪ Fin sz,
      ∀u : rows×Fin (parts a),(fields.site u.2).eval processing (u.1.val.val:Word W)=((party u).val:Word W) := by
    cases a with
    | outer phase trial =>
      let tag:=Attempt.outer phase trial
      have mask:=v.catalyst_date_mask P h width r banks src tab dst owners m tag mounted occ
        (v.catalystMaskBounds_at_height P h width r banks src tab dst owners limit tag)
      rw [slot.entryMemory] at mask
      have present (u : Fin (fs tag).market.rows) (live : u∈v.wideBallotRows h width r banks src tab dst owners tag entry) :
          u.val<2^h:=
        v.payload_live_lt P h width phase trial ((guard C tag).apply entry) u (u.isLt.trans_le fits)
          (mask.live (fs tag).stockSource u live)
      let names:=@SiteNaming.labels (ColumnSite (PayloadStrip.Columns (Stages h D)) k) inferInstance inferInstance
      let owner:=SiteDirectory.payloadRoots _ present
      let sites:=SiteDirectory.payloadParties (d:=D) (k:=k) π
      refine ⟨SiteDirectory.selectedParties _ owner sites names,?_⟩
      rintro ⟨u,l⟩
      let root:=owner u
      let col:=(v.payloadPricePorts P h width).column
      have atCol:=v.payload_row_placement_of_fields P h width π groups packed rfl order co
        (all.base.board tag).columns (all.base.board tag).input all.base.loaded cols root (v.date_prefix_fit h).le
      have bounds:=v.wide_ballot_column_fit h width tag occ room
      have measured (c) : (col c).eval processing (root.val:Word W)=
          (((Fintype.equivFin _) (payloadPlace π root c)).val:Word W) := by
        rw [PrefixAgreement.expr (col c) processing co ((A).endAddress v.mesh)
          (PrefixAgreement.inputEnd_of_fits _ (bounds c)) preserved (root.val:Word W)]
        apply Fin.ext
        rw [Fin.val_cast_of_lt (((Fintype.equivFin _) (payloadPlace π root c)).isLt.trans_le cols)]
        exact atCol.1 c
      rw [v.widePacket_site h width bits siteROM stride old new tag l]
      exact SiteDirectory.payload_partyField π names col processing root sitePage siteSize measured l
    | inner ph tr sj ti =>
      let tag:=Attempt.inner ph tr sj ti
      obtain ⟨hp,ht,hj,hi⟩:=scheduled_inner v.mesh ph tr sj ti occ
      let p : Fin (v.mesh.inject+v.mesh.cool):=⟨ph,hp⟩
      let t : Fin v.mesh.outerFuel:=⟨tr,ht⟩
      let j : Fin v.mesh.reserveSteps:=⟨sj,hj⟩
      let z : Fin v.mesh.innerFuel:=⟨ti,hi⟩
      let born:=finProdFinEquiv (p,t)
      let marks:=days born
      have unique:=v.paid_days_exclusive h width r banks src tab dst owners m born
      have present (u : Fin (fs tag).market.rows) (live : u∈v.wideBallotRows h width r banks src tab dst owners tag entry) :
          ∃path : LiveChains v.sampler π v.depth marks,(BoughtLocation.relative path).val=u.val:=by
        have original : u∈v.wideBallotRows h width r banks src tab dst owners tag (entryMemory C m tag) := by
          rw [slot.entryMemory]
          exact live
        have due:=v.wide_paid_paths h width r banks src tab dst owners π m p t j z boot «public» room mounted
          late small limit layout stored u original
        obtain ⟨path,id⟩:=due
        exact ⟨path,congrArg Fin.val id⟩
      let names:=@SiteNaming.labels (ColumnSite (ChainStrip.Columns v.depth) k) inferInstance inferInstance
      let owner:=SiteDirectory.purchaseRoots _ present
      let sites:=SiteDirectory.boughtParties (depth:=v.depth) π v.sampler marks unique
      refine ⟨SiteDirectory.selectedParties _ owner sites names,?_⟩
      rintro ⟨u,l⟩
      let path:=owner u
      have num : (BoughtLocation.relative path).val=u.val.val:=(present u.val u.property).choose_spec
      have cells:=v.purchased_table_room h late
      let col:=(v.purchasedPricePorts P h width p t).column
      have atCol:=v.purchased_row_placement_of_fields P h width π groups packed rfl rfl order co p t
        (all.base.board tag).columns (all.base.board tag).strata all.base.loaded cols marks unique path
        (all.ports p t (BoughtLocation.keyOf path)) cells.1 cells.2.1 stages degree
        (v.date_prefix_fit h).le le_rfl catRoom
      have bounds:=v.wide_ballot_column_fit h width tag occ room
      have measured (c) : (col c).eval processing (u.val.val:Word W)=
          (((Fintype.equivFin (Columns h D)) (SiteDirectory.stageOrd (allStripColumns v.sampler π v.depth marks unique (path,c)))).val:Word W) := by
        rw [←num,allStripColumns_single]
        rw [PrefixAgreement.expr (col c) processing co ((A).endAddress v.mesh)
          (PrefixAgreement.inputEnd_of_fits _ (bounds c)) preserved ((BoughtLocation.relative path).val:Word W)]
        let value := (Fintype.equivFin (Columns h D)) (CatalogueRows.retainedCol π marks path c)
        change (col c).eval co ((BoughtLocation.relative path).val:Word W)=(value.val:Word W)
        exact Fin.ext ((atCol.1 c).trans (Fin.val_cast_of_lt (value.isLt.trans_le cols)).symm)
      rw [v.widePacket_site h width bits siteROM stride old new tag l]
      exact SiteDirectory.bought_partyField π v.sampler marks unique names col processing path
        (u.val.val:Word W) sitePage siteSize measured l
  let selected : Finset (Fin (sh (.attempt a)).candidates) := rows
  refine ⟨party,identify,?_⟩
  apply scatter_ballot (p:=sh (.attempt a)) (sites:=sz) selected party rom start fields processing safe
  · intro i j
    exact votes i j
  · exact identify

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
