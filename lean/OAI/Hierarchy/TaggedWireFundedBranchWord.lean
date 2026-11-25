import OAI.Hierarchy.TaggedWireFundedElectedRow
import OAI.Hierarchy.TaggedWireBranchRead

namespace OAI
/-! # The encoded ballot read at its actual accepted original event -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
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

local notation "slab" => v.slab (v.seed P h width) P width
local notation "EF" => Slab.effects slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
  (P).catalogue banks source table target owners
local notation "pageRoom" => v.original_selector_room P h width (dims).words.addresses
local notation "copyRoom" => v.original_copy_room P h width r banks source table target owners (dims).copies
local notation "floorE" e => (A).base v.mesh e
local notation "ceilE" e => (A).base v.mesh e+(A).stride
local notation "top" => (A).endAddress v.mesh

namespace FundedDate
section
variable {v h width size π seed age budget small} {e : Event} {tail : List Event}
    {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (e::tail) x}
    {c : ((v.wideSelector h width age budget small).format.slot e).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
local notation "originalEntry" => run C H.prior (origin H.code)

theorem ballot_word : (slots e).word x c=(L).read e originalEntry := by
  rw [←(L).read_install e ((slots e).word x c) x]
  apply (L).read_congr
  intro j
  have right:=Slab.page_end slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
    (P).catalogue banks source table target owners pageRoom copyRoom e
  exact H.current _ ((Nat.add_lt_add_left j.isLt _).trans_le right)

end
section
variable {v h width size π seed age budget small} {a : Attempt} {tail : List Event}
    {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x}
    {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)

local notation "originalEntry" => run C H.prior (origin H.code)

theorem ballot_observed (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) :
    (reader).format.observed a x originalEntry := by
  have before:=(v.funded_ballot_views h width size extent π seed age budget small t c).1
  constructor
  · intro i
    exact (before.1 i).trans (congrArg Fin.val (H.ballot extent i).2.1)
  · intro i
    let batch := PurchaseStage.enabledBatch ((C).layout a) (repair C a)
    let copies := ((C).raw a).batch.copies
    change (if batch.selected (HistogramShelf.snapshot C a x) (i.val : Word w) then copies else 0) =
      (if batch.selected (HistogramShelf.snapshot C a originalEntry) (i.val : Word w) then copies else 0)
    rw [(H.ballot extent i).2.2]

end
end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
