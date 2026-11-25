import OAI.Hierarchy.TaggedWireFundedAttemptRows
import OAI.Hierarchy.TaggedWireReportedPath

namespace OAI
/-! # Assembly of the signed chronological row operators over all original tags -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
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
local notation:max "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape ChosenPackets CoreBoard.PhysicalTerm LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

def rowScheduleHeight := max v.ballotHeight
  (max (Classical.choose (eventually_atTop.1 v.repair_word_room))
    (max v.paidBallotHeight (max v.cursorReplayHeight (max v.feedOperatorHeight (max v.reportHeight v.wideFundedHeight)))))

variable (expanse : v.wideFundedSize h width v.maxBits≤ size)
    (late : v.rowScheduleHeight≤h) (floor : v.widthFloor≤width) (word : v.ReportWordRoom h width)
local notation "tall" => (max_le_iff.mp late).1
local notation "room" => (max_le_iff.mp late).2
local notation "num" => (max_le_iff.mp room).1
local notation "fee" => (max_le_iff.mp ((max_le_iff.mp room).2)).1
local notation "graphs" => (max_le_iff.mp ((max_le_iff.mp room).2)).2
local notation "replay" => (max_le_iff.mp graphs).1
local notation "feeds" => (max_le_iff.mp ((max_le_iff.mp graphs).2)).1
local notation "reports" => (max_le_iff.mp ((max_le_iff.mp graphs).2)).2
local notation "state" => v.wideOrigin h width size seed
local notation "U" => v.wideCursorWidth h width size

def with_elected_rows
    (incoming : ∀(p : Equiv.Perm (Row h)) {a tail x} (t : WireTelescope.CalendarTape.Prefix slots es (state p) (.attempt a::tail) x),
      v.sourceRows h width size extent p seed age budget small t tall floor)
    (outgoing : ∀(p : Equiv.Perm (Row h)) {a tail x} (t : WireTelescope.CalendarTape.Prefix slots es (state p) (.attempt a::tail) x),
      v.targetRows h width size extent p seed age budget small t tall floor) :
    CalendarTerms F h D k width (fuel v.mesh*width) v.radius 1 slots es state := by
  let terms (p : Equiv.Perm (Row h)) (e : Event) {tail x} (t : WireTelescope.CalendarTape.Prefix slots es (state p) (e::tail) x) :
      {T : ∀c : (slots e).choice x,SiteMatrix (State (U p seed age budget small t))
          (State (U p seed age budget small (t.advance c))) F //
        ∀y,(raw F (U p seed age budget small t)).coeff y=∑c,SiteMatrix.act (T c)
          (raw F (U p seed age budget small (t.advance c))).coeff y}:=by
    cases e with
    | attempt a =>
      exact v.attempt_from_rows h width size extent p seed age budget small t tall floor num fee expanse
          (max_le_iff.mp reports).2 replay (incoming p t) (outgoing p t)
    | feed b =>
      exact v.wide_cursor_feed h width size extent p seed age budget small t feeds
  exact {
    width:=fun p _ _ t=>U p seed age budget small t
    head:=fun p=>v.wide_cursor_head h width size extent p seed age budget small
    operator:=fun p {e} _ _ t=>(terms p e t).1
    step:=fun p {e} _ _ t=>(terms p e t).2
    reported:=fun p=>v.wide_reported_path h width size p seed age budget small expanse (max_le_iff.mp reports).1 word
  }

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
