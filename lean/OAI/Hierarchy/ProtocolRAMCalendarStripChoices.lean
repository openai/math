import OAI.Hierarchy.ProtocolRAMCalendarStripElection
import OAI.Hierarchy.ProtocolRAMCalendarElectionBatch
import OAI.Hierarchy.ProtocolRAMCalendarElectionScore
import OAI.Hierarchy.TaggedWireCausalTape

namespace OAI
/-! # Shape of the genuine histogram choice before its counters are examined -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen
open StripDirectory WireTelescope
open scoped Classical Fin.CommRing
variable {z d k q depth r : ℕ}
local notation "actualStages" => List.length (Fabric.shapes (permutationFabric z d))
local notation "W" => wordBits z d copies
variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial width cap : ℕ) (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "A" => arena v s
local notation "B" => install v s c
local notation "C" => chart F c A initial width cap B finish prices catalogue r banks src tbl dst owners
local notation "profiles" => formats F c A initial B

/-- These are public numeric bank endpoints, independent of every private
word, the running stock or which ballots the machine selects. -/
structure ElectionPages {z d k q digits ports : ℕ} (b : StripDirectory.Boards z d k q digits ports)
    (old cut w N : ℕ) : Prop where
  price : b.price.base+b.price.size≤cut
  scores : GlobalTests.stop b.globalTests z N k+2^b.globalTests.indexBits≤cut
  stock : old+b.old.size≤cut
  candidates : b.menu.base+b.menu.size≤cut
  alphabet : b.terms.base+b.terms.size≤cut
  distance : b.test.table.base+b.test.table.size≤cut
  cap : b.maxWidth<2^w
  threshold : b.test.failure.cut<2^w

def beforeTables (a : Attempt) : Prop :=
  let old := (profiles a).market.shelf.stockBase
  let cut := (A).base c (.attempt a)
  match a with
  | .outer p h=>ElectionPages ((B).outer p h) old cut W actualStages
  | .inner p h j t=>ElectionPages ((B).inner p h j t) old cut W actualStages ∧
      (purchasedChannels (z:=z) (d:=d) (k:=k) ((B).outer p h).market.shelf (B).sampler depth ((B).stratumHeader p h)).Before cut

theorem ElectionPages.offsets {digits ports q z d k w old cut N : ℕ} (b : StripDirectory.Boards z d k q digits ports)
    (h : ElectionPages b old cut w N) :
    (GlobalTests.offsets b.globalTests).base+(GlobalTests.offsets b.globalTests).size≤cut := by
  have last:=h.scores
  change b.globalTests.base+2^b.globalTests.indexBits≤cut
  unfold GlobalTests.stop at last
  omega

set_option maxHeartbeats 2000000 in
theorem ballot_before (a : Attempt) (left right : Memory W)
    (same : Below ((A).base c (.attempt a)) left right) (hl : ready C (.attempt a) left)
    (hr : ready C (.attempt a) right) (w4 : 4≤2^W) (space : (A).base c (.attempt a)<2^W)
    (pages : beforeTables v s F c initial a) (i : Fin ((C).layout a).candidates) :
    let sl:=HistogramShelf.snapshot C a left
    let sr:=HistogramShelf.snapshot C a right
    let row:Word W:=(i.val:Word W)
    let b:=enabledBatch ((C).layout a) (repair C a)
    b.packet.eval sl row=b.packet.eval sr row ∧
      b.termCount.read sl (b.packet.eval sl row)=b.termCount.read sr (b.packet.eval sr row) ∧
      (b.selected sl row↔b.selected sr row) := by
  let low:=(A).base c (.attempt a)
  let active:=(profiles a).market.shelf.stockBase
  let sl:=HistogramShelf.snapshot C a left
  let sr:=HistogramShelf.snapshot C a right
  let outerPorts := Fintype.card (PayloadRole actualStages k)
  let innerPorts := Fintype.card (PurchasedRole depth k)
  have cells:=before_snapshot v s F c initial width cap finish prices catalogue banks src tbl dst owners a left right same hl hr
  cases a with
  | outer p h =>
    let u:=(B).outer p h
    let channel:=payloadChannels z actualStages k
    let menu:=payloadMenu F actualStages k (B).positive (B).radius (B).radius_nonneg (B).tolerance (B).tolerance_pos
      ((B).tree (.outer p h)) ((B).tree_nonneg _) (B).minimum
    let prev:Bank:={u.old with base:=active}
    let test:={u.test with live:=channel.live,rows:=(profiles (.outer p h)).market.rows,population:=2^z}
    have reached:=payload_before z actualStages k low
    have t:ElectionPages u active low W actualStages:=pages
    have failure:=Channels.Before.failure_fits channel reached u.test u.price (GlobalTests.offsets u.globalTests) prev
      ((profiles (.outer p h)).market.rows) (2^z) t.price (t.offsets u) t.stock t.distance space
    let tests := (repair C (.outer p h)).tests
    have mask:=before_mask (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners (.outer p h)
      left right same hl hr w4 (GlobalTests.score_before u.globalTests z actualStages k tests.excess.out tests.excess.bound false prev low space t.scores t.stock)
      (GlobalTests.score_before u.globalTests z actualStages k tests.payload.out tests.payload.bound true prev low space t.scores t.stock) failure t.threshold i
    exact Channels.Before.padded_election (q:=q) channel reached menu test u.price (GlobalTests.offsets u.globalTests)
      u.terms u.menu (repair C (.outer p h)).repairBits u.selectors prev u.copies u.maxWidth
      (max outerPorts innerPorts) sl sr (i.val:Word W) cells mask space t.cap
      (Nat.le_max_left outerPorts innerPorts) t.price (t.offsets u) t.stock t.candidates t.alphabet
  | inner p h j b =>
    let u:=(B).inner p h j b
    let channel:=purchasedChannels (z:=z) (d:=d) (k:=k) ((B).outer p h).market.shelf (B).sampler depth ((B).stratumHeader p h)
    let menu:=purchasedMenu F depth k (B).positive (B).radius (B).radius_nonneg (B).tolerance (B).tolerance_pos
      ((B).tree (.inner p h j b)) ((B).tree_nonneg _) (B).minimum
    let prev:Bank:={u.old with base:=active}
    let test:={u.test with live:=channel.live,rows:=(profiles (.inner p h j b)).market.rows,population:=2^z}
    obtain ⟨t,reached⟩:=pages
    have failure:=Channels.Before.failure_fits channel reached u.test u.price (GlobalTests.offsets u.globalTests) prev
      ((profiles (.inner p h j b)).market.rows) (2^z) t.price (t.offsets u) t.stock t.distance space
    let tests := (repair C (.inner p h j b)).tests
    have mask:=before_mask (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners (.inner p h j b)
      left right same hl hr w4 (GlobalTests.score_before u.globalTests z actualStages k tests.excess.out tests.excess.bound false prev low space t.scores t.stock)
      (GlobalTests.score_before u.globalTests z actualStages k tests.payload.out tests.payload.bound true prev low space t.scores t.stock) failure t.threshold i
    exact Channels.Before.padded_election (q:=q) channel reached menu test u.price (GlobalTests.offsets u.globalTests)
      u.terms u.menu (repair C (.inner p h j b)).repairBits u.selectors prev u.copies u.maxWidth
      (max outerPorts innerPorts) sl sr (i.val:Word W) cells mask space t.cap
      (Nat.le_max_right outerPorts innerPorts) t.price (t.offsets u) t.stock t.candidates t.alphabet

theorem choice_before (R : CalendarTape.CounterROM C) (a : Attempt) (left right : Memory W)
    (same : Below ((A).base c (.attempt a)) left right) (hl : ready C (.attempt a) left)
    (hr : ready C (.attempt a) right) (w4 : 4≤2^W) (space : (A).base c (.attempt a)<2^W)
    (pages : beforeTables v s F c initial a)
    (alphabet : ∀i,CalendarTape.CounterROM.measured («C»:=C) a right i≤q) :
    R.format.observed a left right := by
  have elected:=ballot_before v s F c initial width cap finish prices catalogue banks src tbl dst owners
    a left right same hl hr w4 space pages
  constructor
  · intro i
    change min (CalendarTape.CounterROM.measured («C»:=C) a left i) q=CalendarTape.CounterROM.measured («C»:=C) a right i
    rw [show CalendarTape.CounterROM.measured («C»:=C) a left i=CalendarTape.CounterROM.measured («C»:=C) a right i from
      congrArg Fin.val (elected i).2.1,Nat.min_eq_left (alphabet i)]
  · intro i
    simp only [CalendarTape.CounterROM.format,CalendarTape.CounterROM.copies,(elected i).2.2]

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
end

end OAI
