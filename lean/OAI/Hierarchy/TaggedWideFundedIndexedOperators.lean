import OAI.Hierarchy.TaggedWideIndexedCursor
import OAI.Hierarchy.TaggedWireFundedRowSchedule

namespace OAI
/-! # Executed packet and feed operators at an original path index -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged CalendarTape ChosenPackets ThreeFlat.RAM
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Filter
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width size : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "K" => siteLast h D k+1
local notation "es" => events v.mesh
local notation "place" => siteNumber h D k
local notation "order" => wideRouteOrder h D k
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
variable (extent : (A).endAddress v.mesh≤ size) (π : Equiv.Perm (Row h)) (seed : Boot.Tape h D)
    (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "slots" => (v.wideSelector h width age budget small).format.slot
local notation "L" => (v.wideSelector h width age budget small).format.windows
local notation "state" => v.wideOrigin h width size seed
local notation "base" => (state) π
local notation "origin" key => v.wideOrigin h width size ((L).header es key seed) π
local notation "Visit" ev => Prefix.PathVisit slots es base ev
variable (expanse : v.wideFundedSize h width v.maxBits≤ size)
    (late : v.rowScheduleHeight≤h) (floor : v.widthFloor≤width) (word : v.ReportWordRoom h width)
local notation "tall" => (max_le_iff.mp late).1
local notation "rest" => (max_le_iff.mp late).2
local notation "numeric" => (max_le_iff.mp rest).1
local notation "fees" => (max_le_iff.mp ((max_le_iff.mp rest).2)).1
local notation "graphs" => (max_le_iff.mp ((max_le_iff.mp rest).2)).2
local notation "replay" => (max_le_iff.mp graphs).1
local notation "feeds" => (max_le_iff.mp ((max_le_iff.mp graphs).2)).1
local notation "reports" => (max_le_iff.mp ((max_le_iff.mp graphs).2)).2
variable
    (incoming : ∀(perm : Equiv.Perm (Row h)) {a tail x} (t : WireTelescope.CalendarTape.Prefix slots es ((state) perm) (.attempt a::tail) x),
      v.sourceRows h width size extent perm seed age budget small t tall floor)
    (outgoing : ∀(perm : Equiv.Perm (Row h)) {a tail x} (t : WireTelescope.CalendarTape.Prefix slots es ((state) perm) (.attempt a::tail) x),
      v.targetRows h width size extent perm seed age budget small t tall floor)
local notation "Z" => v.with_elected_rows h width size extent seed age budget small expanse late floor word incoming outgoing
local notation "beginAt" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix slots es base es base)
local notation "ws" => Prefix.atWidth ((Z).width π)
local notation "cs" => Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=base)
local notation "step" => Prefix.atStep ((Z).width π) ((Z).operator π)
local notation "gateAt" path:arg j:arg => indexedStep cs ws step es (Prefix.atCursor beginAt) (Prefix.histories beginAt path) j
local notation "selected" path:arg j:arg => Prefix.pathVisit beginAt path j

section Attempt
variable {a : Attempt} (z : Visit (.attempt a))
local notation "ref" => v.wide_reference_date h width size extent π seed age budget small z.prior
local notation "date" c => v.wide_funded_date h width size extent π seed age budget small z.prior c
local notation "u" => (es).length-(Event.attempt a::z.tail).length
local notation "o" => v.nativeSlots P h width a
local notation "goodsGraph" => CoreBoard.ordinalGoods π.symm place o
local notation "axisGraph" => catalystGraph place
local notation "pre" => (P).catalogue.coreMount π.symm place (v.wideOrder h width) z.mem
local notation "past" => v.wirePaidAt h width v.maxBits u z.mem
local notation "bal" => fun i=>v.wireGoodsAt h width u z.mem ((o).symm i)
local notation "remaining" c => fun axis=>(fuel v.mesh*width-v.wireUsedAt h width u z.mem axis)-(date c).reserveDebit axis
local notation "spares" => (pre).actual.chordWidths past+
  (goodsGraph).chordWidths (fun i=>(bal) i-(date (ref).1).debit i)+(axisGraph).chordWidths (remaining (ref).1)
local notation "carry" => (pre).actual.chordWidths past+(date z.choice).afterMount.actual.chordWidths (date z.choice).paid+
  (axisGraph).chordWidths (remaining z.choice)
local notation "transfer" => FeedTransfer.afterVote o (fun c=>(date c).afterGoods) (fun c=>(date c).spill) z.choice

/-- Both factors retain their original domains, with the actual elected signed
packet entries first and the weighted clipping walks second. -/
def electedAttemptAt {U V : Widths K} (gate : SiteMatrix (State U) (State V) F) : Prop :=
  Through (PassMatrix.matrix (fun i choice=>(((ref).2.tender extent tall floor) i).entry choice) spares z.choice)
    (FeedTransfer.matrix (F:=F) (date z.choice).afterMount (place).injective (publicChord h D k)
      (ProtocolRAMDateSpillRank.spillEnum (date z.choice).afterMount order) carry transfer) gate

end Attempt

/-- The feed includes its funded calendar cut, original consecutive states,
and deterministic transfer with the same original commodity occurrence order. -/
def electedFeedAt {b : Boundary} (z : Visit (.feed b))
    {U V : Widths K} (gate : SiteMatrix (State U) (State V) F) : Prop :=
  ∃(key : Bits (CalendarTape.bits slots es)) (past : List Event)
    (_ : Calendar.Slot C (origin key) (.feed b) past z.tail z.mem) (day : Fin (es).length)
    (tag : (es)[day.val]=.feed b),
    day.val=past.length ∧ StockBound.state C (origin key) day.val=z.mem ∧
    StockBound.state C (origin key) (day.val+1)=after C (.feed b) z.mem ∧
    v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits ((L).header es key seed))
      feeds budget small v.maxBits day b tag gate

def electedOperatorAt (e : Event) (z : Visit e)
    {U V : Widths K} (gate : SiteMatrix (State U) (State V) F) : Prop := by
  cases e with
  | attempt a => exact v.electedAttemptAt h width size extent π seed age budget small late floor z gate
  | feed b => exact v.electedFeedAt h width size extent π seed age budget small late z gate

attribute [local irreducible] attempt_from_rows wide_cursor_feed wide_funded_date wide_reference_date

private theorem elected_operator_rebase (e : Event) (z : Visit e) {U V : Widths K}
    (gate : SiteMatrix (State U) (State V) F)
    (same : Prefix.IndexedOperator ((Z).operator π z.prior z.choice) gate) :
    v.electedOperatorAt h width size extent π seed age budget small late floor e z gate := by
  rw [same.matrix]
  cases e with
  | attempt a =>
    have fact := v.attempt_factors h width size extent π seed age budget small z.prior tall floor numeric fees
      expanse (max_le_iff.mp reports).2 replay (incoming π z.prior) (outgoing π z.prior) z.choice
    exact Through.relabel fact same.entry same.next
  | feed b =>
    obtain ⟨key,past,cut,day,tag,index,pre,post,receipt⟩ :=
      v.cursor_feed_presents h width size extent π seed age budget small z.prior feeds
    refine ⟨key,past,cut,day,tag,index,pre,post,?_⟩
    exact FeedTransfer.Presents.rebase _ (receipt z.choice) same.entry same.next

/-- This is the original branch of the selected date on the literal encoded
history. The two neighboring width identifications are computed by replay. -/
theorem wide_elected_indexed_operator (path : Path slots es base) (j : Fin (es).length) :
    v.electedOperatorAt h width size extent π seed age budget small late floor ((es).get j) (selected path j)
      (gateAt path j) :=
  v.elected_operator_rebase h width size extent π seed age budget small expanse late floor word incoming outgoing
    ((es).get j) (selected path j) _ (Prefix.indexed_operator ((Z).width π) ((Z).operator π) path j)

/-- Retain the actual continuation of this day in its native funded receipt. -/
def indexedFundedDate (path : Path slots es base) (j : Fin (es).length) :=
  let z:=selected path j
  v.wide_funded_date_with h width size extent π seed age budget small z.prior z.choice z.future

theorem indexedFundedDate_code (path : Path slots es base) (j : Fin (es).length) :
    (v.indexedFundedDate h width size extent π seed age budget small path j).code=
      CalendarTape.encode slots es base path := by
  exact congrArg (CalendarTape.encode slots es base) (Prefix.pathVisit_suffix beginAt path j)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
