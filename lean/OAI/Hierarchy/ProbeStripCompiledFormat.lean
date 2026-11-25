import OAI.Hierarchy.ProbeStripDirectoryCore
import OAI.Hierarchy.ProbeStripPortDestination
import OAI.Hierarchy.ProbeStripMenuDebitFields
import OAI.Hierarchy.ProbeStripMenuLookup
import OAI.Hierarchy.ProtocolRAMNativeOccurrenceFormat
import OAI.Hierarchy.ProtocolRAMNativeGlobalTests
import OAI.Hierarchy.ProtocolRAMStripFailureWords
import OAI.Hierarchy.TaggedWireShelf

namespace OAI
/-! # The original native finite-menu repair, stock sources and signed strip board -/
noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage ProbeStage PurchaseFrozen
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing Classical BigOperators

variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E → Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}
  {q goods digits radix w : ℕ} {D : Type*} [Fintype D]

/-- The local dynamic quotes are gathered from their actual global
coordinates, using the public price offset and the authoritative stock bank. -/
def quoted (price offsets stocks : Bank) (addr : Fin digits → Expr) (j : Fin digits) : Expr :=
  (AttemptGate.valueTerm price offsets stocks).atRow (addr j)

def tested (layout : StripTest digits) (price offsets stocks : Bank) (addr : Fin digits → Expr) :
    StripTest digits := {layout with quoted := quoted price offsets stocks addr}

/-- Only inventory roles check the global stock. A printed cash role
receives its exact allowance, since its debit is settled on the cash tape. -/
def inventory (stocks : Bank) (required : Expr) : Option Expr → Expr
  | some slot => .lookup stocks slot
  | none => required

/-- The batch uses the same ordered price words as the failure score, and the
same zero-reserved packet numbers used by the immutable finite menu. -/
def batch (m : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms menu enabled selectors stocks : Bank) (owner : Expr) (copies maxWidth : ℕ)
    (ports : Fin goods → E) (slot : Fin goods → Option Expr) : Batch q goods :=
  let prices := List.ofFn test.quoted
  let packet := menuLookup menu test.radix prices
  let perCopy (e : Fin goods) := entry m packet (fun i => useBits m i (ports e))
  ⟨copies,test.radix,maxWidth,prices,menu,terms,enabled,owner,
   WireTelescope.HistogramShelf.field selectors,
   fun e => inventory stocks (boundedMul maxWidth (.lit copies) (perCopy e)) (slot e),perCopy⟩

def wires (m : Probe.FixedMenu F edge req box ε tree N) (b : Batch q goods)
    (ports : Fin goods → E) (e : Fin goods) (j : Fin q) : Expr :=
  entry m b.packet (fun i => installedBits m i (ports e) j)

def sources (h : Calendar.StockCommit.PortHeader) (global : ℕ)
    (old reserve half price : Bank) (mode : Expr) (m : Probe.FixedMenu F edge req box ε tree N)
    (b : Batch q h.ports) (ports : Fin h.ports → E) (slot : Fin h.ports → Option Expr) :
    Calendar.StockCommit.Sources :=
  h.sources old reserve half price mode (destination h global slot) b (wires m b ports)

/-- The two maps share the same local demanded occurrences and physical wire roles. -/
structure Channels (A E : Type*) where
  address : A → Expr
  account : E → Option A
  live : Expr

def Channels.slot (c : Channels A E) (e : Fin (Fintype.card E)) : Option Expr :=
  (c.account ((Fintype.equivFin E).symm e)).map c.address

def Channels.digit (c : Channels A E) (i : Fin (Fintype.card A)) : Expr :=
  c.address ((Fintype.equivFin A).symm i)

def payloadChannels (z stageCount k : ℕ) :
    Channels (PayloadStrip.Quotes stageCount k) (ColumnWires.Role (PayloadStrip.Columns stageCount)
      (Fin (PayloadStrip.edgeCount stageCount)) (PayloadStrip.Quotes stageCount k ⊕ Empty) k) :=
  ⟨payloadSlot z,ColumnWires.account id,.branch .lt .row (.lit (2^z)) (.lit 1) (.lit 0)⟩

def purchasedChannels {z d k : ℕ} (sh : Shelf) (S : PurchaseSampler) (depth : ℕ)
    (start : ℕ) :
    Channels (ChainStrip.Axes depth k) (ColumnWires.Role (ChainStrip.Columns depth)
      (Fin (ChainStrip.edgeCount depth)) (ChainStrip.Axes depth k ⊕ Unit) k) :=
  ⟨allChainSlot (z:=z) (d:=d) sh S depth (stratumHeader z d k S.degree depth start),
    ColumnWires.account id,.lookup (flagBank sh S z d k depth) .row⟩

/-- The common market score, batch admits, port widths and scatter commit are
placed in one calendar record. Other public shelf locations come from the
row layout. Both stock readers use the market's authoritative snapshot. -/
def format {z d k : ℕ} (c : Channels D E) (m : Probe.FixedMenu F edge req box ε tree N)
    (market : Calendar.Market z d k) (repair : Repair q (Fintype.card E))
    (test : StripTest (Fintype.card D)) (globalTests : Calendar.GlobalTests.Layout) (baseline : ℝ)
    (price terms menu enabled selectors : Bank)
    (old reserve half cash : Bank) (owner report : Expr) (priceOut : ℕ→ℕ)
    (copies maxWidth start indexBits limit : ℕ) :
    Calendar.Format z d k q (Fintype.card E) :=
  let stocks := {old with base:=market.shelf.stockBase}
  let test := tested {test with live:=c.live,rows:=market.rows,population:=2^z} price (Calendar.GlobalTests.offsets globalTests) stocks c.digit
  let ports := (Fintype.equivFin E).symm
  let b := batch m test terms menu enabled selectors stocks owner copies maxWidth ports c.slot
  let tabs := wires m b ports
  let board : Repair q (Fintype.card E) := { repair with
    purchaseLink := {repair.purchaseLink with lengthCode := .lit 1}
    batch := b
    priceOut := fun i => priceOut i.val
    wire := tabs
    tests := Calendar.GlobalTests.board globalTests z (permutationFabric z d).shapes.length k repair.tests stocks baseline
    reportWidth := fun j => chooseField (Fintype.card E) 0 (fun i => tabs i j) report }
  let header : Calendar.StockCommit.PortHeader := ⟨start,market.rows,Fintype.card E⟩
  let global := PurchaseInventory.footprint z (permutationFabric z d).shapes.length k
  let actualMarket := {market with failures:=test.failure}
  let src := sources header global stocks reserve half cash (Calendar.word board.modeOut) m b ports c.slot
  let p : Calendar.Format z d k q (Fintype.card E) :=
    ⟨actualMarket,board,copies,indexBits,src,header.count,global,limit⟩
  p.withOccurrenceHeader start

/-- Recompile both the gate price lookups and all per-ball admissions against
the one real predecessor bank selected by the chronological layout. -/
def formatAtStock {z d k : ℕ} (c : Channels D E) (m : Probe.FixedMenu F edge req box ε tree N)
    (market : Calendar.Market z d k) (repair : Repair q (Fintype.card E))
    (test : StripTest (Fintype.card D)) (globalTests : Calendar.GlobalTests.Layout) (baseline : ℝ)
    (price terms menu enabled selectors : Bank) (old reserve half cash : Bank)
    (owner report : Expr) (priceOut : ℕ→ℕ) (copies maxWidth start indexBits limit active : ℕ) :=
  format (z:=z) (d:=d) (k:=k) c m {market with shelf:={market.shelf with stockBase:=active}} repair test globalTests baseline
    price terms menu enabled selectors old reserve half cash owner report priceOut copies maxWidth start indexBits limit


end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
