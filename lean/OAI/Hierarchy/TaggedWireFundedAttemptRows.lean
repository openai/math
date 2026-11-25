import OAI.Hierarchy.TaggedWireFundedPurchasedLedger
import OAI.Hierarchy.TaggedWireBranchDebitPass

namespace OAI
/-! # The signed operator from the exact packet rows of one physical calendar attempt -/

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

open Filter CalendarTape ChosenPackets LinearAlgebra.SpectralBooks ChordGraph
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

/-- Numerically the left sides are the same elected tiles for every choice; the right sides refer
to receipts in the original stage on the independently admitted tape for that very choice. -/
def sourceRows : Prop := ∀c : choice,(∑j,((rows) j).input)=(G).chordWidths (date c).debit+(K).chordWidths (date c).reserveDebit

def targetRows : Prop := ∀c : choice,(∑j,((routes) j).post (c j))=(G).chordWidths (date c).gain+
  (date c).afterMount.actual.chordWidths (date c).paid

variable (numeric : Classical.choose (eventually_atTop.1 v.repair_word_room)≤h)
  (paidAge : v.paidBallotHeight≤h) (expanse : v.wideFundedSize h width v.maxBits≤ size)
  (capAge : v.wideFundedHeight≤h) (graphAge : v.cursorReplayHeight≤h)

local notation "past" => v.wirePaidAt h width v.maxBits u x
local notation "bal" => fun i=>v.wireGoodsAt h width u x ((o).symm i)
local notation:max "remaining" c:arg => fun z=>(fuel v.mesh*width-v.wireUsedAt h width u x z)-(date c).reserveDebit z
local notation "passive" => (pre).actual.chordWidths past+
  (G).chordWidths (fun i=>(bal) i-(date ((ref).1)).debit i)+(K).chordWidths (remaining ((ref).1))
local notation:max "carry" c:arg => (pre).actual.chordWidths past+(date c).afterMount.actual.chordWidths (date c).paid+
  (K).chordWidths (remaining c)
local notation:max "transfer" c:arg => FeedTransfer.afterVote o (fun d : choice=>(date d).afterGoods)
  (fun d : choice=>(date d).spill) c

private def attemptWithFactors
    (incoming : v.sourceRows h width size extent π seed age budget small t tall floor)
    (outgoing : v.targetRows h width size extent π seed age budget small t tall floor) :
    {T : ∀c : choice,SiteMatrix (State (shape t)) (State (shape (t.advance c))) F //
      (∀y,(raw F (shape t)).coeff y=∑c,SiteMatrix.act (T c) (raw F (shape (t.advance c))).coeff y) ∧ ∀ c : choice,
    Through (PassMatrix.matrix (fun i ballot=>((routes) i).entry ballot) passive c)
      (FeedTransfer.matrix (F:=F) (date c).afterMount (siteNumber h D k).injective (publicChord h D k)
        (ProtocolRAMDateSpillRank.spillEnum (date c).afterMount order) (carry c) (transfer c))
      (T c)} := by
  let board:=fun c : choice=>(date c).afterMount
  let visits:=fun c : choice=>ProtocolRAMDateSpillRank.spillEnum (board c) order
  let oldPaid:=v.wirePaidAt h width v.maxBits u x
  let goods:=fun i=>v.wireGoodsAt h width u x ((o).symm i)
  let reserve:=fun z=>fuel v.mesh*width-v.wireUsedAt h width u x z
  let mk:=FeedTransfer.measuredAttempt (siteNumber h D k).injective (publicChord h D k) o rows routes
    (ref).1 board visits (pre).actual oldPaid (fun c=>(date c).afterPaid) goods
    (fun c=>(date c).debit) reserve (fun c=>(date c).reserveDebit) (fun c=>(date c).nextReserve)
    (fun c=>(date c).paid) (fun c=>(date c).gain) (fun c=>(date c).afterGoods) (fun c=>(date c).spill)
    incoming outgoing (fun c=>(date c).input_funds extent tall floor numeric)
    (fun c i=>((date c).reserve_account extent expanse capAge i).1)
    (fun c=>(date c).account extent tall floor numeric) (fun c=>(date c).prior_ends extent paidAge)
    (fun c=>(date c).paid_account extent paidAge) (fun c i=>((date c).reserve_account extent expanse capAge i).2)
  have first : (pre).actual.chordWidths oldPaid+(G).chordWidths goods+(K).chordWidths reserve=shape t:=by
    rw [ordinalGoods_width]
    have same : goods ∘ o=v.wireGoodsAt h width u x:=by
      funext i
      simp only [goods,Function.comp_apply,Equiv.symm_apply_apply]
    rw [same]
    rfl
  have last (c : choice) : FeedTransfer.ledger (π:=π.symm) («place»:=place) (board c).actual
      (date c).afterPaid ((date c).afterGoods ∘ o) (date c).nextReserve=shape (t.advance c):=by
    rw [(date c).next_graph extent graphAge]
    unfold FeedTransfer.ledger
    have same : (date c).afterGoods ∘ o=v.wireGoodsAt h width ((date c).prior.length+1)
        (after C event (run C (date c).prior (origin ((date c).code)))):=by
      funext i
      simp only [FundedDate.afterGoods,Function.comp_apply,Equiv.symm_apply_apply]
    rw [same]
    rfl
  refine ⟨fun c=>rebase first (last c) (mk.1 c),rebase_family first last mk.1 mk.2,?_⟩
  intro c
  exact Through.relabel (FeedTransfer.measured_factors (siteNumber h D k).injective (publicChord h D k) o rows routes
    (ref).1 board visits (pre).actual oldPaid (fun c=>(date c).afterPaid) goods
    (fun c=>(date c).debit) reserve (fun c=>(date c).reserveDebit) (fun c=>(date c).nextReserve)
    (fun c=>(date c).paid) (fun c=>(date c).gain) (fun c=>(date c).afterGoods) (fun c=>(date c).spill)
    incoming outgoing (fun c=>(date c).input_funds extent tall floor numeric)
    (fun c i=>((date c).reserve_account extent expanse capAge i).1)
    (fun c=>(date c).account extent tall floor numeric) (fun c=>(date c).prior_ends extent paidAge)
    (fun c=>(date c).paid_account extent paidAge) (fun c i=>((date c).reserve_account extent expanse capAge i).2) c) first (last c)

def attempt_from_rows
    (incoming : v.sourceRows h width size extent π seed age budget small t tall floor)
    (outgoing : v.targetRows h width size extent π seed age budget small t tall floor) :
    {T : ∀c : choice,SiteMatrix (State (shape t)) (State (shape (t.advance c))) F //
      ∀y,(raw F (shape t)).coeff y=∑c,SiteMatrix.act (T c) (raw F (shape (t.advance c))).coeff y} :=
  let fact := v.attemptWithFactors h width size extent π seed age budget small t tall floor numeric paidAge expanse capAge graphAge incoming outgoing
  ⟨fact.1,fact.2.1⟩

/-- The actual calendar coefficient contracts precisely the fixed originally selected signed
packet matrices and then its measured native clipping walk, on their common intermediate bits. -/
theorem attempt_factors
    (incoming : v.sourceRows h width size extent π seed age budget small t tall floor)
    (outgoing : v.targetRows h width size extent π seed age budget small t tall floor) (c : choice) :
    Through (PassMatrix.matrix (fun i ballot=>((routes) i).entry ballot) passive c)
      (FeedTransfer.matrix (F:=F) (date c).afterMount (siteNumber h D k).injective (publicChord h D k)
        (ProtocolRAMDateSpillRank.spillEnum (date c).afterMount order) (carry c) (transfer c))
      ((v.attempt_from_rows h width size extent π seed age budget small t tall floor numeric paidAge
        expanse capAge graphAge incoming outgoing).1 c) :=
  (v.attemptWithFactors h width size extent π seed age budget small t tall floor numeric paidAge expanse capAge graphAge incoming outgoing).2.2 c

include numeric paidAge expanse capAge graphAge in
theorem signed_shapes
    (incoming : v.sourceRows h width size extent π seed age budget small t tall floor)
    (outgoing : v.targetRows h width size extent π seed age budget small t tall floor) (c : choice) :
    passive+∑i,((rows) i).input=shape t ∧
    passive+∑i,((routes) i).post (c i)=FeedTransfer.input (π:=π.symm) («place»:=place) (carry c) (transfer c) := by
  obtain ⟨entry,middle,exit,gate⟩:=v.attempt_factors h width size extent π seed age budget small t tall floor
    numeric paidAge expanse capAge graphAge incoming outgoing c
  exact ⟨entry,middle⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
