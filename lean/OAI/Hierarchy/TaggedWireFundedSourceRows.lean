import OAI.Hierarchy.TaggedWireFundedDebitDate
import OAI.Hierarchy.TaggedWireFundedEarnedDebits
import OAI.Hierarchy.TaggedWireFundedElectedDebit
import OAI.Hierarchy.TaggedWireMeasuredDemand
import OAI.Hierarchy.TaggedWireFundedAttemptRows

namespace OAI
/-! # Measured input of every original elected packet, including opposite-radius withdrawals -/

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
local notation:max "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape ChosenPackets LinearAlgebra.SpectralBooks ChordGraph
open PurchaseFrozen PurchaseStage StockCommit RepairHistogram Strip StripDirectory CatalogueRows
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators

variable {a : Attempt} {tail x} (t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x)
  (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "event" => Event.attempt a
local notation "u" => (es).length-(event::tail).length
local notation "ref" => v.wide_reference_date h width size extent π seed age budget small t
local notation:max "date" c:arg => v.wide_funded_date h width size extent π seed age budget small t c
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


local notation "fmt" => (reader).format
local notation "ballot" => enabledBatch ((C).layout a) (repair C a)
local notation "I" => Fin ((C).layout a).candidates
local notation:max "picked" i:arg => (ballot).selected (HistogramShelf.snapshot C a x) ((i).val:Word w)
local notation:max "atom" i:arg hh:arg => ((ref).2.packetAt extent tall floor i hh)
local notation "root" => v.wideBallotRoot h a
local notation "menu" => fun i hi=>(atom i hi).menu root
local notation "arity" => fun i hi=>(atom i hi).arity root
local notation "rt" => fun i hi=>(atom i hi).route root (publicChord h D k)
local notation "area" => (v.nativeFormats P h width a).pricedArea
local notation "sources" => (v.nativeFormats P h width a).stockSource
local notation "fee" => v.stamp P h width r banks source table target owners a
local notation "msk" => v.earnedClass P h width a
local notation "opp" => v.earnedMate P h width a
local notation "key" => pairKeys (Columns h D) k
local notation "pad" => publicChord h D k

/-- Classify each actual native consumed port once. An ordinary debit is attached to its
original commodity and a catalyst debit uses the retired pair address of its original occurrence. -/
theorem funded_source_rows (expanse : v.wideFundedSize h width v.maxBits≤ size) (capAge : v.wideFundedHeight≤h) :
    v.sourceRows h width size extent π seed age budget small t tall floor := by
  classical
  let _ : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  intro c
  let H:=date c
  let old:=(ref).2
  let plan:=H.stripPlan extent tall floor (dims).strip
  let day:=H.originalDebitDate expanse capAge
  let paid:=v.stage P h width r banks source table target owners a (run C H.prior (origin H.code))
  let view:=(v.funded_ballot_views h width size extent π seed age budget small t c).1
  let debitAt := fun originalRole : (Σ _ : I, Fin (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))) =>
    if on : picked originalRole.1 then (atom originalRole.1 on).installed.debitWire pad originalRole.2 else pad
  let wire := fun port : Fin (area).occurrences => debitAt (plan.enum.symm port)
  have known (i : I) (on : picked i) (j : Fin _) :
      wire (plan.enum ⟨i,j⟩)=(atom i on).installed.debitWire pad j:=by
    change debitAt (plan.enum.symm (plan.enum ⟨i,j⟩)) = _
    rw [Equiv.symm_apply_apply]
    exact dite_eq_left on
  have row (i : I) (on : picked i) : ((rows) i).input=Probe.optionWidths (fun p=>wire (plan.enum ⟨i,p⟩))
      (fun p=>consumedBits (fresh area sources).columns paid (plan.enum ⟨i,p⟩)):=by
    simp only [known i on]
    exact H.same_debit_row extent tall floor i on pad old
  have typed:=all_debit_ports (a:=area) («s»:=sources) (post:=paid) plan day key G K wire (H.posted_debits extent tall floor day)
    (by
      intro i active slot
      have pick:=(H.priced_row_iff extent tall floor i).mp active
      let occ := plan.enum ⟨i,slot⟩
      let amount := consumedBits (n:=(area).occurrences) (fresh area sources).columns paid occ
      refine (congrArg (fun chord => Finsupp.single chord amount) (known i pick slot)).trans ?_
      exact H.routed_original_debit old extent tall floor expanse capAge i pick pad slot)
  have measured:=(fmt).measured_source a x x paid area sources G K view menu arity plan wire
    (day.physicalCatalystKey key) (fun i=>day.entry.bits (Fin.cast day.shape.symm i)) c
    (fun i off active=>off ((H.priced_row_iff extent tall floor i).mp active)) row typed
  exact measured.trans (congrArg (fun amounts => (G).chordWidths H.debit + (K).chordWidths amounts)
    (H.reserve_terms expanse capAge))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
