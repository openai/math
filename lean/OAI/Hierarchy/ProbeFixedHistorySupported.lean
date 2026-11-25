import OAI.Hierarchy.ProbeFixedWideEventCode
import OAI.Hierarchy.ProbeFixedRecordedCommodity
import OAI.Hierarchy.ProtocolRAMCataloguePaidSupport

namespace OAI
/-! All paid slices of an actual attempt address only earlier purchased candidates
or original core links. The recorded role selector also covers inactive rows. -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

private theorem supported_of_core {w : ℕ} (b : Board) (s : PaidWidths.Slice) (m : Memory w)
    (always : ∀i : Fin s.count,(s.edge.eval m (i.val:Word w)).val<b.coreRows) : b.Supported s m := by
  intro i j hit
  have lt:=always i
  rw [hit] at lt
  change b.coreRows+j.val<b.coreRows at lt
  omega

private theorem read_at_same_row {w u v : ℕ} (m : Memory w) (x y : Expr) (same : u = v)
    (read : x.eval m (u : Word w) = y.eval m (u : Word w)) :
    x.eval m (v : Word w) = y.eval m (v : Word w) :=
  same ▸ read

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "C" => v.wideSignedChart h width stock


local notation "b" => (P).catalogue
local notation "fmt" => v.nativeFormats P h width
local notation "H" => StripChart.header F s
local notation "dim" => max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A fmt (P).joint.initial width v.keepLimit
local notation "spills" => v.paidSpillPath P h width (routeBanks start cnt r) route order
local notation "boundary" => v.paidFeedPath P h width route lay
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (b).sink r banks src tab dst owners

set_option maxHeartbeats 700000 in
theorem supported_below (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (o : Orders h D k) (raw : Boot.Tape h D) (word : (A).endAddress v.mesh<2^w) (m : Memory w)
    (same : ∀x<(A).first,m x=v.wideSignedMidAt h width size stock M π o raw x)
    (narrow : dim≤2^w) (room : (b).rows<2^w) (bits : ℕ)
    (early : ∀a,Event.attempt a∈events v.mesh→∀i : Fin (spills a).positions,
      ((spills a).edge.eval m (i.val:Word w)).val<(b).coreRows)
    (feeds : ∀a,Event.feed a∈events v.mesh→∀c∈(lay a).columns,∀i : Fin ((boundary a c).positions),
      ((boundary a c).edge.eval m (i.val:Word w)).val<(b).coreRows) :
    ∀ ev∈events v.mesh, ∀slice∈v.wideEventSlices h width bits ev,(b).Supported slice m := by
  obtain ⟨_,_,_,econ,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock M π o raw word
  let E:=v.publicHeader P h width
  have low:=(E.ports.end_le 0).trans (v.catalyst_ports_le_first P h width)
  have hdr (a : Attempt) : (H a).Loaded m :=
    (v.catalyst_header P h width a) ▸ (econ.ports 0).frame (fun x _ hx=>same x (hx.trans_le low))
  intro ev dated s0 member
  cases ev with
  | feed a =>
    obtain ⟨c,mem,rfl⟩:=List.mem_map.mp member
    exact supported_of_core b _ m (feeds a dated c mem)
  | attempt a =>
    let H':=H a
    let ids:=StripChart.id F s b a
    let label:=(fmt a).labelSource sink (b).idBase H'.fieldTerm ids
    let direct:=PaidWidths.paidDirect (fmt a).pricedArea (fmt a).stockSource label
    let T:=tree a
    let S:=spills a
    have cases' : s0=direct ∨ s0∈(fmt a).mateSlices T ∨
        s0=PaidWidths.paidBroadcast (fmt a).pricedArea T.positions T.owner T.parity T.edge T.sourceRow
          (fmt a).board.batch.copies bits ∨
        s0=PaidWidths.paidSpill (fmt a).pricedArea S.positions S.owner S.parity S.edge S.sourceRow := by
      simpa only [wideEventSlices,eventSlices,Format.paidSlices,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,or_assoc] using member
    have guard : ∃ old,T=(b).guardWalk old := by cases a <;> exact ⟨_,rfl⟩
    rcases cases' with rfl|mate|rfl|rfl
    · intro i j hit
      let idx:=finCongr (v.occurrence_count P h width a) i
      let f : Fin dim := ((H a).enum.symm idx).2
      have field:((H a).fieldTerm.eval m (i.val:Word w)).val=f.val :=
        (congrArg Fin.val ((hdr a).second idx)).trans (Fin.val_cast_of_lt (f.isLt.trans_le narrow))
      have pick := eval_chooseField dim 0 ids H'.fieldTerm m (i.val:Word w) f
        (by simpa only [Nat.zero_add] using narrow) (by simpa only [Nat.zero_add] using field)
      have observed := v.recorded_commodity_id_below h width size extent stock M π o raw word m same a dated f idx room
      have rowValue : idx.val = i.val := rfl
      have recorded := read_at_same_row m (ids f) ((b).commonID (StripChart.edge F s (b).rows a f))
        rowValue observed
      change (((chooseField dim 0 ids H'.fieldTerm).eval m (i.val:Word w))-((b).idBase:Word w)).val=_ at hit
      rw [pick, recorded, (b).commonID_sub] at hit
      exact (b).checked_hit _ _ _ j room hit
    · obtain ⟨old,guarded⟩:=guard
      rw [guarded] at mate
      cases ht : old.catalystMate with
      | none => simp [Format.mateSlices,Board.guardWalk,ht] at mate
      | some pair =>
        simp [Format.mateSlices,Board.guardWalk,ht] at mate
        subst s0
        exact fun i j hit=>(b).checked_hit pair.2 _ _ j room hit
    · obtain ⟨old,guarded⟩:=guard
      exact (b).walk_supported _ old m room (congrArg Traversals.edge guarded)
    · exact supported_of_core b _ m (early a dated)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
