import OAI.Hierarchy.TaggedWireFundedRowSchedule
import OAI.Hierarchy.TaggedWireFundedSourceRows
import OAI.Hierarchy.TaggedWireFundedTargetRows

namespace OAI
/-! # Routing of every elected signed packet on the authentic chronological native tape -/

noncomputable section
set_option quotPrecheck false
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


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
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

open Filter CalendarTape ChosenPackets CoreBoard.PhysicalTerm LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

def routingHeight := max v.rowScheduleHeight (max v.earnedTreeHeight v.earnedEndsHeight)

include extent in
/-- For every physical permutation and original private ballot, the same signed row family
produces the measured state on the next date and the original final checked report. -/
def routedSchedule (expanse : v.wideFundedSize h width v.maxBits≤ size) (late : v.routingHeight≤h)
    (floor : v.widthFloor≤width) (word : v.ReportWordRoom h width) :
    CalendarTerms F h D k width (fuel v.mesh*width) v.radius 1 slots es (v.wideOrigin h width size seed) := by
  have limits:=max_le_iff.mp late
  have levels:=max_le_iff.mp limits.1
  have allAges:=limits.1
  simp only [rowScheduleHeight,max_le_iff] at allAges
  have paidAge : v.wideFundedHeight≤h:=allAges.2.2.2.2.2.2
  exact v.with_elected_rows h width size extent seed age budget small expanse limits.1 floor word
    (fun p {_ _ _} t=>v.funded_source_rows h width size extent p seed age budget small t levels.1 floor expanse paidAge)
    (fun p {_ _ _} t=>v.funded_target_rows h width size extent p seed age budget small t levels.1 floor
      (max_le_iff.mp limits.2).1 (max_le_iff.mp limits.2).2)

/-- The calibrated schedule supplies both tensor-side widths for the actual
attempt at any reachable prefix and its original ballot. -/
abbrev routed_factors {a : Attempt} {tail x}
    (t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x) (c : (slots (.attempt a)).choice x)
    (expanse : v.wideFundedSize h width v.maxBits≤ size) (late : v.routingHeight≤h)
    (floor : v.widthFloor≤width) :=
  let levels:=max_le_iff.mp late
  let dates:=max_le_iff.mp levels.1
  let cost:=max_le_iff.mp dates.2
  let paid:=max_le_iff.mp cost.2
  let replay:=max_le_iff.mp paid.2
  let endRoom:=max_le_iff.mp (max_le_iff.mp replay.2).2
  v.attempt_factors h width size extent π seed age budget small t dates.1 floor cost.1 paid.1 expanse
    endRoom.2 replay.1
    (v.funded_source_rows h width size extent π seed age budget small t dates.1 floor expanse endRoom.2)
    (v.funded_target_rows h width size extent π seed age budget small t dates.1 floor
      (max_le_iff.mp levels.2).1 (max_le_iff.mp levels.2).2) c

abbrev routed_shapes {a : Attempt} {tail x}
    (t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x) (c : (slots (.attempt a)).choice x)
    (expanse : v.wideFundedSize h width v.maxBits≤ size) (late : v.routingHeight≤h)
    (floor : v.widthFloor≤width) :=
  let law:=v.routed_factors h width size extent π seed age budget small t c expanse late floor
  And.intro (Classical.choose law) (Classical.choose (Classical.choose_spec law))

abbrev routed_output_width {a : Attempt} {tail x}
    (t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x) (c : (slots (.attempt a)).choice x)
    (expanse : v.wideFundedSize h width v.maxBits≤ size) (late : v.routingHeight≤h)
    (floor : v.widthFloor≤width) :=
  let law:=v.routed_factors h width size extent π seed age budget small t c expanse late floor
  Classical.choose (Classical.choose_spec (Classical.choose_spec law))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
