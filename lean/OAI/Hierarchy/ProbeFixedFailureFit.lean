import OAI.Hierarchy.ProbeMarketStockBounds
import OAI.Hierarchy.ProbeFixedMarketFootprint
import OAI.Hierarchy.ProbeFixedElectionPages
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # The actual failed-purchase procedure fits the machine at each dated slot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StripDirectory PurchaseFrozen
open scoped Fin.CommRing Classical

private def failureOperand {z d k q ports : ℕ} {A E : Type*} [Fintype A]
    (b : StripDirectory.Boards z d k q (Fintype.card A) ports) (ch : Channels A E)
    (old rows : ℕ) :=
  (tested {b.test with live:=ch.live, rows:=rows, population:=2^z} b.price
    (GlobalTests.offsets b.globalTests) {b.old with base:=old} ch.digit).failure

private theorem failureOperand_fits {z d k q ports old cut w stages : ℕ}
    {A E : Type*} [Fintype A] (b : StripDirectory.Boards z d k q (Fintype.card A) ports)
    (ch : Channels A E) (rows : ℕ) (pages : Slab.ElectionPages b old cut w stages)
    (before : ch.Before cut) (word : cut < 2^w) :
    (failureOperand b ch old rows).effective.Fits w cut :=
  Channels.Before.failure_fits ch before b.test b.price (GlobalTests.offsets b.globalTests)
    {b.old with base:=old} rows (2^z) pages.price (Slab.ElectionPages.offsets b pages)
    pages.stock pages.distance word

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "d" => (2^v.W)
local notation "N" => CoreBoard.Stages z d
local notation "A" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "fmt" => v.nativeFormats P z width
local notation "W" => wordBits z d copies

set_option cleanup.letToHave false
set_option maxHeartbeats 900000

private theorem compiled_outer_failure {letters : ℕ} (s : StripChart.Boards z d k letters v.depth)
    (phase trial incoming : ℕ) :
    let f := build F s (.outer phase trial) incoming
    f.market.failures = failureOperand (s.outer phase trial) (payloadChannels z N k)
      f.market.shelf.stockBase f.market.rows := by
  rfl

private theorem compiled_inner_failure {letters : ℕ} (s : StripChart.Boards z d k letters v.depth)
    (phase trial slice inner incoming : ℕ) :
    let f := build F s (.inner phase trial slice inner) incoming
    let ch := purchasedChannels (z:=z) («d»:=d) (k:=k) (s.outer phase trial).market.shelf
      s.sampler v.depth (s.stratumHeader phase trial)
    f.market.failures = failureOperand (s.inner phase trial slice inner) ch
      f.market.shelf.stockBase f.market.rows := by
  rfl

theorem market_failure_fits (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (capacity : (A).endAddress v.mesh<2^W)
    (maximum : v.menu.maximum<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (directory : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    let m:=(fmt a).atTime v.mesh v.finish (v.basePhase width) a
    m.failures.pass.Fits W := by
  let low:=(A).base v.mesh (.attempt a)
  let m:=(fmt a).atTime v.mesh v.finish (v.basePhase width) a
  have pre:=v.market_regions P z width a
  have word : low<2^W :=
    ((Nat.le_add_right ..).trans ((A).within v.mesh (.attempt a) scheduled)).trans_lt capacity
  have upper:=v.market_capacity P z width a scheduled capacity
  have first : m.shelf.firstBase≤ m.flags := by unfold Market.flags Shelf.flagsBase;omega
  refine ⟨⟨trivial,?_,trivial,trivial⟩,(pre.2.1.trans (pre.2.2.1.trans
    (first.trans (Nat.le_add_right ..)))).trans_lt upper⟩
  apply ProtocolRAMGeneratedWrite.fits_mono _ pre.1
  have pages:=v.election_pages P z width a maximum threshold directory
  have actualArena : Slab.arena (v.slab (v.seed P z width) P width) B = A := rfl
  simp only [Slab.beforeTables,v.nativeBoards_install P z width,actualArena] at pages
  cases a with
  | outer p h =>
    let u:=(B).outer p h
    let ch:=payloadChannels z N k
    let incoming:=resolvedStock v.mesh A P.joint.initial (build F B) (.outer p h)
    let f:=build F B (.outer p h) incoming
    have actual := compiled_outer_failure v z B p h incoming
    change f.market.failures.effective.Fits W low
    rw [actual]
    exact failureOperand_fits u ch f.market.rows pages (payload_before z N k low) word
  | inner p h j t =>
    let u:=(B).inner p h j t
    let ch:=purchasedChannels (z:=z) («d»:=d) (k:=k) ((B).outer p h).market.shelf (B).sampler v.depth ((B).stratumHeader p h)
    let incoming:=resolvedStock v.mesh A P.joint.initial (build F B) (.inner p h j t)
    let f:=build F B (.inner p h j t) incoming
    have actual := compiled_inner_failure v z B p h j t incoming
    change f.market.failures.effective.Fits W low
    rw [actual]
    exact failureOperand_fits u ch f.market.rows pages.1 pages.2 word

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
