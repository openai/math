import OAI.Hierarchy.TaggedWireFundedTargetTransport
import OAI.Hierarchy.TaggedWireFundedEarnedTarget

namespace OAI
/-! # Original archived credits supply every output row of a fixed signed ballot -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
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


variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
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

open Filter CalendarTape ChosenPackets LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

variable {a : Attempt} {tail x} (t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x)
  (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "event" => Event.attempt a
local notation "u" => (es).length-(event::tail).length
local notation "ref" => v.wide_reference_date h width size extent π seed age budget small t
local notation "date" c => v.wide_funded_date h width size extent π seed age budget small t c
local notation "choice" => (slots event).choice x
local notation "rows" => (ref).2.row extent tall floor
local notation "routes" => (ref).2.tender extent tall floor
local notation "o" => v.nativeSlots P h width a
local notation "place" => siteNumber h D k
local notation "G" => CoreBoard.ordinalGoods π.symm place o
local notation "K" => catalystGraph place
local notation "b" => (P).catalogue
local notation "pre" => (b).coreMount π.symm place (v.wideOrder h width) x
local notation "shape" => v.wideCursorWidth h width size π seed age budget small

theorem funded_target_rows (tree : v.earnedTreeHeight≤h) (ends : v.earnedEndsHeight≤h) :
    v.targetRows h width size extent π seed age budget small t tall floor :=
  v.target_from_earned h width size extent π seed age budget small t tall floor
    (v.earned_target_rows h width size extent π seed age budget small t tall floor tree) ends

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
