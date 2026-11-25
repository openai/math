import OAI.Hierarchy.TaggedWireTerminalVector
import OAI.Hierarchy.TaggedWireFundedCursor
import OAI.Hierarchy.ProbeFixedWirePaidEnds
import OAI.Hierarchy.ProbeFixedWideFundedAlignment
import OAI.Hierarchy.ProbeFixedWidePaidTotal

namespace OAI
/-! # Original numbered terminal report for every complete path -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
attribute [local irreducible] Nat.pow
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
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open CalendarTape CoreBoard.PhysicalTerm
open Filter
local notation "last" => (es).length
local notation "ceiling" => (A).endAddress v.mesh

/-- Density and physical word-size bounds at a wide induction parent hold
uniformly over all tags, all original tape extensions and every edge ordinal. -/
def ReportWordRoom :=
  ∀n,ceiling≤n→∀(p : Equiv.Perm (Row h))(tape : Boot.Tape h D),
    let chk:=v.wideSignedCheckoutAt h width n stock v.radius p order tape
    chk ceiling=0→∀e : Fin (P).catalogue.rows,
      PaidWidths.total (v.widePaidSlices h width v.maxBits) chk e+
        (v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w

def reportHeight :=
  max (max v.wideFundedHeight (Classical.choose (eventually_atTop.1 v.wide_funded_alignment)))
    (max (Classical.choose (eventually_atTop.1 v.wire_paid_ends))
      (Classical.choose (eventually_atTop.1 v.wide_wire_paid)))

theorem cofinal_report_sources {κ B : ℝ} :
    ∀ᶠ p : WideParent κ B in WideParent.large κ B,
      v.reportHeight≤p.h ∧ v.ReportWordRoom p.h p.w := by
  have tall : Tendsto (WideParent.h (κ:=κ) («A»:=B)) (WideParent.large κ B) atTop:=tendsto_comap
  filter_upwards [tall.eventually (eventually_ge_atTop v.reportHeight),v.cofinal_terminal_bill (κ:=κ) (B:=B) v.maxBits]
    with p hh fee
  exact ⟨hh,fee⟩

variable (expanse : v.wideFundedSize h width v.maxBits≤ size) (late : v.reportHeight≤h)
    (room : v.ReportWordRoom h width)
local notation "curr" => v.wideCursorWidth h width size π seed age budget small
local notation "fullPath" => Path slots es base

/-- Keep the original report fields definitionally fixed while replacing
only the terminal equality of the charged width vector. -/
def Report.transportLedger {h d k «w» R M den : ℕ} {p : Equiv.Perm (Row h)} {U «V»}
    (Z : CoreBoard.Report p d k «w» R M den U) (eqn : U=«V») :
    CoreBoard.Report p d k «w» R M den «V»:={Z with ledger:=Z.ledger.trans eqn}

include expanse late room in
def wide_reported_path (j : fullPath) :
    CoreBoard.Report π D k width (fuel v.mesh*width) v.radius 1 (curr (CalendarTape.Prefix.finish CalendarTape.Prefix.start j)) := by
  classical
  let b:=encode slots es base j
  let raw:=(L).header es b seed
  let tape:=v.wideFundedRaw h width v.maxBits raw
  let entered:=origin b
  let chk:=v.wideSignedCheckoutAt h width size stock v.radius π.symm order tape
  have stableHeight := (le_max_right _ _).trans late
  have paidAge : Classical.choose (eventually_atTop.1 v.wide_wire_paid)≤h:=(le_max_right ..).trans stableHeight
  have endAge : Classical.choose (eventually_atTop.1 v.wire_paid_ends)≤h:=(le_max_left ..).trans stableHeight
  have preAge := (le_max_left _ _).trans late
  have admitted : v.wideFundedHeight≤h:=(le_max_left ..).trans preAge
  have nameAge : Classical.choose (eventually_atTop.1 v.wide_funded_alignment)≤h:=(le_max_right ..).trans preAge
  have bound:=(v.wide_funded_extent h width v.maxBits).trans expanse
  have est:=room size bound π.symm tape (v.wide_funded_path h width age budget small v.maxBits size bound v.radius π.symm seed j)
  let names {entries : ℕ} (site : Fin entries→Fin num) (fees : Fin entries→ℕ) := Classical.choose_spec (eventually_atTop.1 v.wide_funded_alignment) h nameAge width v.maxBits size expanse
    small budget π.symm raw site fees (fun i=>(CatalystArchive.pairKeys (Columns h D) k i).val)
  have pay:=(Classical.choose_spec (eventually_atTop.1 v.wide_wire_paid) h paidAge width small budget
    size bound π.symm tape v.maxBits).1 last le_rfl
  have close:=Classical.choose_spec (eventually_atTop.1 v.wire_paid_ends) h endAge width small budget
    size bound π.symm tape v.maxBits last le_rfl
  have done (mem : Memory w) : StockBound.state C mem last=run C es mem := by
    change run C ((es).take (es).length) mem=_
    rw [List.take_length]
  rw [done] at pay close
  let resultReport:=v.native_state_report h width size π.symm raw v.maxBits expanse admitted budget small est 0
    (fun site fees=>names site fees) pay close
  apply Report.transportLedger resultReport
  change v.wireAt h width v.maxBits π.symm last (run C es entered)=
    v.wireAt h width v.maxBits π.symm ((es).length-0) (CalendarTape.terminal slots es base j)
  rw [Nat.sub_zero,v.wide_funded_execution h width size bound π seed age budget small j]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
