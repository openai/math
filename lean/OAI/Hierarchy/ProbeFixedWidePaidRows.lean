import OAI.Hierarchy.ProbeFixedPaidRows
import OAI.Hierarchy.ProbeFixedWidePaidReadout
import OAI.Hierarchy.ProbeFixedPaidBirth
import OAI.Hierarchy.ProbeFixedPaidFit
import OAI.Hierarchy.ProbeFixedWideBirthRows
import OAI.Hierarchy.ProbeFixedPaidEconomicRows

namespace OAI
/-! # Paid row geometry of the true original wide native tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open PurchaseFrozen RepairHistogram StockBound StockCommit StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (h width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "S" => v.nativeBoards P h width
local notation "E" => v.publicHeader P h width
local notation "A" => v.privateArena P h width
local notation "G" => v.stamp P h width r banks src tab dst owners
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "b" => (P).catalogue
local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
local notation "bh" => StripChart.header F S
variable (π : Equiv.Perm (Fin (2^h)))
local notation "seen[" m "]" => CoreRoute.Seen order v.radius groups packed socket v.depth π m


local notation "form" => v.nativeFormats P h width
local notation "pre" => v.stage P h width r banks src tab dst owners
local notation "D" => max (Fintype.card (PayloadRole (Stages h (2^v.W)) k)) (Fintype.card (PurchasedRole v.depth k))
variable (m : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "days" => v.birthMarks P h width r banks src tab dst owners m
local notation "layout[" a "]" => TrialLayout C a (form a).pricedArea (form a).stockSource (G a) v.keepLimit width
  ((A).base v.mesh (.attempt a))

section Bought
variable (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice : Fin v.mesh.reserveSteps) (inner : Fin v.mesh.innerFuel)
local notation "outer" => Attempt.outer phase.val trial.val
local notation "ev" => Attempt.inner phase.val trial.val slice.val inner.val
local notation "orig" => entryMemory C m outer
local notation "before" => entryMemory C m ev
local notation "born" => finProdFinEquiv (phase,trial)
local notation "bc" => v.ballot P h width r banks src tab dst owners ev
local notation "prior" => resolvedStock v.mesh A (P).joint.initial (build F S) ev
variable (boot : CoreRoute.Seen (v.wideOrder h width) v.radius (WideMemory.groups h v.W)
      (WideMemory.dir h v.W k v.wideJobs) (v.wideSources h width).2 v.depth π m)
    («public» : (v.publicHeader (v.widePlacement h width) h width).Resident m)
    (endRoom : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh <
      2^(Native.wordBits h (2^v.W) Native.copies))
    (whole : Calendar.mounted (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners)
      (events v.mesh) m) (late : v.stripHeight≤h) (small : width≤2^h)
    (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h)
    (layout : TrialLayout (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners)
      (.inner phase.val trial.val slice.val inner.val)
      (v.nativeFormats (v.widePlacement h width) h width (.inner phase.val trial.val slice.val inner.val)).pricedArea
      (v.nativeFormats (v.widePlacement h width) h width (.inner phase.val trial.val slice.val inner.val)).stockSource
      (v.stamp (v.widePlacement h width) h width r banks src tab dst owners (.inner phase.val trial.val slice.val inner.val))
      v.keepLimit width ((v.privateArena (v.widePlacement h width) h width).base v.mesh
        (.attempt (.inner phase.val trial.val slice.val inner.val))))

include boot «public» endRoom whole in
omit [Nonempty (Fin k)] in
private theorem outer_base : v.WideForestBase h width π orig := by
  apply v.wide_forest_base h width π boot «public» endRoom
  exact entryMemory_low C A m outer whole
    (fun t x hx=>(v.event_prefix P h width r banks src tab dst owners t x hx).1)

include boot «public» endRoom whole late small threshold layout in
def wide_paid_local :
    PurchasedLocal F S v.mesh b (P).routes phase trial slice.val inner.val prior C before (G ev) π groups packed v.copyScale width :=
  v.purchasedLocal (R:=(b).coreRows) h width (P).joint b groups packed socket r banks src tab dst owners m π
    phase trial slice inner whole late small (v.wideGeometryPrefix h width).2.1 (v.wideGeometryPrefix h width).2.2
    ((v.outer_base h width r banks src tab dst owners π m phase trial boot «public» endRoom whole).board outer)
    threshold layout

local notation "localPaid" => v.wide_paid_local h width r banks src tab dst owners π m phase trial slice inner
  boot «public» endRoom whole late small threshold layout

include boot «public» endRoom whole late small threshold layout in
theorem wide_paid_marks (room : ArchiveRoom C m (v.mesh.inject+v.mesh.cool))
    (live : ∃j,j∈liveRows bc (pre ev before) (form ev).market.rows) :
    days born=actualMarks ({((S).outer phase.val trial.val).market.shelf with stockBase:=(localPaid).receipt.stock} : Shelf)
      (localPaid).receipt.phase (localPaid).receipt.price (localPaid).receipt.kind (localPaid).receipt.frozen (k:=k) :=
  v.committed_birth_marks (R:=(b).coreRows) h width (P).joint b groups packed socket r banks src tab dst owners m π
    phase trial slice inner whole room late small (v.wideGeometryPrefix h width).2.1 (v.wideGeometryPrefix h width).2.2
    ((v.outer_base h width r banks src tab dst owners π m phase trial boot «public» endRoom whole).board outer)
    threshold layout live

include boot «public» endRoom whole late small threshold layout in
theorem wide_paid_paths (room : ArchiveRoom C m (v.mesh.inject+v.mesh.cool)) (j : Fin (form ev).market.rows)
    (positive : j∈liveRows bc (pre ev before) (form ev).market.rows) :
    ∃path : LiveChains v.sampler π v.depth (days born), BoughtLocation.relative path=j := by
  rw [v.wide_paid_marks h width r banks src tab dst owners π m phase trial slice inner boot «public» endRoom whole
    late small threshold layout room ⟨j,positive⟩]
  exact (localPaid).owner_paths F S v.mesh b (P).routes phase trial slice.val inner.val prior C before (G ev) j positive

end Bought


omit [Nonempty (Fin k)] in
private theorem paid_occurrence_room (a : Attempt) (occurs : Event.attempt a∈events v.mesh)
    (endRoom : (A).endAddress v.mesh<2^W) : (form a).pricedArea.occurrences≤2^W := by
  obtain ⟨⟨_,_,occ,low⟩,_⟩:=v.paid_economic_headers P h width a occurs
  have count (u : PortHeader) : u.count≤u.stop := by
    have bound:=ProtocolRAMPurchaseSampler.lt_span (2*u.count)
    change u.count≤u.parity.base+ProtocolRAMPurchaseSampler.span (2*u.count)
    omega
  exact occ.le.trans ((count _).trans (low.trans ((Nat.le_add_right ..).trans endRoom.le)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3500000 in
/-- Both positive paid columns of every original event have individual original
row witnesses and the same constant independent of payload height and width.
The supplied observations are derived on either of the two specified tapes by
`wide_paid_run_reads` and `wide_paid_checkout_reads`. -/
theorem wide_paid_at (out : Memory W) (reads : v.WidePaidReadout h width r banks src tab dst owners π m out)
    (boot : seen[m]) («public» : (E).Resident m) (endRoom : (A).endAddress v.mesh<2^W)
    (whole : Calendar.mounted C (events v.mesh) m) (archive : ArchiveRoom C m (v.mesh.inject+v.mesh.cool))
    (late : v.stripHeight≤h) (small : width≤2^h) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h)
    (catFit : (b).rows<2^W) (colFit : Fintype.card (Columns h (2^v.W))≤2^W)
    (stages : Stages h (2^v.W)≤2^W) (degree : v.sampler.degree≤2^W) (fields : D≤2^W)
    (a : Attempt) (earlier later : List Event) (entry : Memory W)
    (slot : Slot C m (.attempt a) earlier later entry) (layout : layout[a])
    (e : Fin (b).rows) (mask mate : Expr) (issued : (v.nativeTrees P h width a).catalystMate=some (mask,mate)) :
    v.PaidAt P h width r banks src tab dst owners π days order rfl a out e mask mate := by
  have occurred : Event.attempt a∈events v.mesh := by
    change Event.attempt a∈events (C).mesh
    rw [slot.events]
    simp
  have num:=v.paid_occurrence_room h width a occurred endRoom
  have dated := reads.base.board a
  have header : (bh a).Loaded out := by
    simpa only [v.catalyst_boards P h width] using dated.port
  have value:=reads.archived a entry earlier later slot layout
  cases a with
  | outer phase trial =>
    have fit:=v.payload_paid_fit P h width r banks src tab dst owners phase trial m entry earlier later slot «public» late small
    let outerDate := Attempt.outer phase trial
    have maskRead := v.catalyst_date_mask P h width r banks src tab dst owners m outerDate whole occurred
      (v.catalystMaskBounds_at_height P h width r banks src tab dst owners threshold outerDate)
    rw [slot.entryMemory] at maskRead
    exact v.payload_paid_at_of_fields P h width r banks src tab dst owners π days order rfl groups packed rfl out reads.base.loaded
      colFit (v.date_prefix_fit h).le catFit fields e mask mate phase trial entry fit dated.columns dated.input header num issued value
      (fun j live => v.payload_live_lt P h width phase trial ((guard C outerDate).apply entry) j
        (j.isLt.trans_le (v.market_rows_fit P h width late outerDate))
        (maskRead.live (form outerDate).stockSource j live))
  | inner u a j t =>
    have bounds : u<v.mesh.inject+v.mesh.cool ∧ a<v.mesh.outerFuel ∧ j<v.mesh.reserveSteps ∧ t<v.mesh.innerFuel := by
      simp only [events,outerBlock,trialBlock,reserveBlock,List.mem_flatMap,List.mem_map,List.mem_range,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at occurred
      aesop
    let phase : Fin (v.mesh.inject+v.mesh.cool):=⟨u,bounds.1⟩
    let trial : Fin v.mesh.outerFuel:=⟨a,bounds.2.1⟩
    let slice : Fin v.mesh.reserveSteps:=⟨j,bounds.2.2.1⟩
    let inner : Fin v.mesh.innerFuel:=⟨t,bounds.2.2.2⟩
    have entryAt:=slot.entryMemory
    subst entry
    let born:=v.wide_paid_local h width r banks src tab dst owners π m phase trial slice inner boot «public» endRoom
      whole late small threshold layout
    have named:=v.wide_paid_marks h width r banks src tab dst owners π m phase trial slice inner boot «public» endRoom
      whole late small threshold layout archive
    have fit:=v.purchased_paid_fit P h width r banks src tab dst owners u a j t m _ earlier later slot «public» late small
    have space:=v.purchased_table_room h late
    exact v.purchased_paid_at_of_fields P h width r banks src tab dst owners π days order rfl groups packed rfl rfl out reads.base.loaded
      colFit (v.date_prefix_fit h).le catFit fields e mask mate phase trial j t _ fit born
      (v.paid_days_exclusive h width r banks src tab dst owners m) named dated.columns dated.strata header
      (fun u=>reads.ports phase trial (BoughtLocation.keyOf u)) space.1 space.2.1 stages degree num issued value

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
