import OAI.Hierarchy.TaggedWireFundedElectedRow
import OAI.Hierarchy.TaggedWireElectedTender
import OAI.Hierarchy.ProbeFixedReadbackProducer

namespace OAI
/-! # The fixed original row family of a funded signed calendar election -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open PurchaseStage WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "input" => fun _ : Equiv.Perm (Row h)=>original
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
open Filter CalendarTape ChosenPackets LinearAlgebra.SpectralBooks ChordGraph
open Native

def wideBallotRoot (a : Attempt) : Fin (v.wideBallotParties h a) := by
  refine ⟨0,?_⟩
  cases a with
  | outer p t=>
    let _ : Nonempty (PayloadStrip.Columns N):=⟨PayloadStrip.first N 0⟩
    exact Fintype.card_pos
  | inner p t layer tick=>
    let _ : Nonempty (ChainStrip.Columns v.depth):=⟨ChainStrip.inlet v.depth 0⟩
    exact Fintype.card_pos

def ballotHeight : ℕ := by
  letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  exact max (Classical.choose (eventually_atTop.1 v.readback_run))
    (max (Classical.choose (eventually_atTop.1 v.wide_row_room))
      (Classical.choose (eventually_atTop.1 v.wide_face_room)))

open scoped Classical
namespace FundedDate
variable {v h width size π seed age budget small}
variable {a : Attempt} {tail : List Event} {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "tape" => v.wideFundedRaw h width v.maxBits ((L).header es H.code seed)
local notation "native" => origin H.code
local notation "batch" => enabledBatch ((C).layout a) (repair C a)
local notation "snapshot" => HistogramShelf.snapshot C a x
local notation "picked" i => (batch).selected snapshot ((i : Fin ((C).layout a).candidates).val:Word w)

include extent tall floor in
def readbackRun : v.ReadbackRun P h width r banks source table target owners π.symm native native :=
  (Classical.choose_spec (eventually_atTop.1 v.readback_run) h (max_le_iff.mp tall).1
    width small floor budget size extent π.symm tape
    ((v.wide_verdict h width size extent v.radius π.symm tape age budget small).mpr H.valid)).some

include extent tall floor in
def packetAt (i : Fin ((C).layout a).candidates) (hit : picked i) : H.ElectedPacket i := by
  letI : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  have rooms:=max_le_iff.mp (max_le_iff.mp tall).2
  have edges:=Classical.choose_spec (eventually_atTop.1 v.wide_row_room) h rooms.1 width
  have faces:=Classical.choose_spec (eventually_atTop.1 v.wide_face_room) h rooms.2
  exact H.electedPacket (H.readbackRun extent tall floor) extent edges.1 faces.1 faces.2.1 faces.2.2 i hit

local notation "u" => H.packetAt extent tall floor
local notation "root" => v.wideBallotRoot h a
local notation "pad" => publicChord h D k
local notation "menu" => fun i hit=>((u) i hit).menu root
local notation "arity" => fun i hit=>((u) i hit).arity root
local notation "view" => (v.funded_ballot_views h width size extent π seed age budget small t c).1
local notation "marks" => v.birthMarks P h width r banks source table target owners native
local notation "ends" => (P).catalogue.physicalEnds (π:=π.symm) («marks»:=marks) (P).routes.directory (v.wideOrder h width) rfl
local notation "shape" => CatalogueRows.installedRows π.symm ends (siteNumber h D k).toEmbedding pad
local notation "fmt" => (reader).format

def row (i : Fin ((C).layout a).candidates) :
    ChosenPackets.Row F (siteLast h D k+1) ((fmt).letters a x i) ((fmt).copies a x i) := by
  letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  exact (fmt).electedRow a x x view menu arity i

def tender (i : Fin ((C).layout a).candidates) : RowRouting (H.row extent tall floor i) shape := by
  letI : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  exact (fmt).electedTender a x x shape view menu arity (fun i hit=>((u) i hit).route root pad) i

end FundedDate

include extent in
/-- Choose one complete admissible suffix to read the common original operands. Its ballot
letters and native placements then define one row family before summing over all histograms. -/
def wide_reference_date {a : Attempt} {tail : List Event} {x : Memory w} (t : CalendarTape.Prefix slots es base (.attempt a::tail) x) :
    Σ c : (slots (.attempt a)).choice x,v.FundedDate h width size π seed age budget small t c := by
  let future:=(v.wide_funded_continuation h width size extent π seed age budget small t).some
  exact ⟨future.1,v.wide_funded_date h width size extent π seed age budget small t future.1⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
