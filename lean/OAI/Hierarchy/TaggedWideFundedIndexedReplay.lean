import OAI.Hierarchy.TaggedWideFundedIndexedRouted
import OAI.Hierarchy.TaggedWireFundedMiddleReplay
import OAI.Hierarchy.TaggedWireFundedFeedReplay
import OAI.Hierarchy.TaggedWireFundedElectedReads

namespace OAI
/-! # Original tape, chronological date, and paid operands of the recovered visit -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar
variable {X : Type} {slot : Event→Slot X} {events : List Event} {start : X}

/-- The length of the unused suffix determines the date even when event labels repeat. -/
theorem pathVisit_date : ∀ {todo x} (p : Prefix slot events start todo x) (path : Path slot todo x)
    (j : Fin todo.length), (pathVisit p path j).tail.length+j.val+1=todo.length
  | [],_,_,_,j => j.elim0
  | e::tail,_,p,⟨c,future⟩,j => by
    refine Fin.cases ?_ (fun i=>?_) j
    · rfl
    · have prev:=pathVisit_date (p.advance c) future i
      simpa only [pathVisit,Fin.cases_succ,Fin.val_succ,List.length_cons] using
        (show (pathVisit (p.advance c) future i).tail.length+(i.val+1)+1=tail.length+1 by omega)
theorem pathVisitAt_eq_cast (path : Path slot events start) (j : Fin events.length) {e : Event}
    (hit : events.get j=e) :
    pathVisitAt path j hit=cast (congrArg (fun f=>PathVisit slot events start f) hit)
      (pathVisit (Prefix.start : Prefix slot events start events start) path j) := by
  subst e
  rfl

end Hierarchy.WireTelescope.CalendarTape.Prefix

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged CalendarTape ChosenPackets ThreeFlat.RAM
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Filter
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 700000
set_option cleanup.letToHave false
set_option Elab.async false
attribute [local irreducible] Nat.pow
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width size : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "es" => events v.mesh
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
variable (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size) (π : Equiv.Perm (Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "base" => v.wideOrigin h width size seed π
local notation "beginAt" => (CalendarTape.Prefix.start : CalendarTape.Prefix slots es base es base)
local notation "visit" path:arg j:arg => CalendarTape.Prefix.pathVisit beginAt path j
local notation "fullDate" path:arg j:arg => v.indexedFundedDate h width size extent π seed age budget small path j

theorem indexedFundedDate_clock (path : Path slots es base) (j : Fin (es).length) :
    (fullDate path j).prior.length=j.val ∧ (es).length-(visit path j).tail.length=j.val+1 := by
  have count:=CalendarTape.Prefix.pathVisit_date beginAt path j
  have finished:=(fullDate path j).clock.2
  omega

/-- In either calendar arm the literal native code and both neighboring dates
survive transporting the recovered visit to its advertised event constructor. -/
theorem indexedFundedDate_at (path : Path slots es base) (j : Fin (es).length)
    {e : Event} (tag : (es).get j=e) :
    let z:=cast (congrArg (fun f=>CalendarTape.Prefix.PathVisit slots es base f) tag) (visit path j)
    let J:=v.wide_funded_date_with h width size extent π seed age budget small z.prior z.choice z.future
    J.code=CalendarTape.encode slots es base path ∧ J.prior.length=j.val ∧
      (es).length-z.tail.length=j.val+1 := by
  subst e
  exact ⟨v.indexedFundedDate_code h width size extent π seed age budget small path j,
    v.indexedFundedDate_clock h width size extent π seed age budget small path j⟩

section Feed
variable (expanse : v.wideFundedSize h width v.maxBits≤ size) (routeAge : v.routingHeight≤h)
    (floor : v.widthFloor≤width) (word : v.ReportWordRoom h width)
local notation "cal" => v.routedSchedule h width size extent seed age budget small expanse routeAge floor word
local notation "rowAge" => (max_le_iff.mp routeAge).1
local notation "sub" => (max_le_iff.mp ((max_le_iff.mp rowAge).2)).2
local notation "graphs" => (max_le_iff.mp sub).2
local notation "feeds" => (max_le_iff.mp ((max_le_iff.mp graphs).2)).1
local notation "cs" => CalendarTape.Prefix.cursorSlot («slot»:=slots) (events:=es) (x₀:=base)
local notation "gate" path:arg j:arg => indexedStep cs (CalendarTape.Prefix.atWidth ((cal).width π)) (CalendarTape.Prefix.atStep ((cal).width π)
  ((cal).operator π)) es (CalendarTape.Prefix.atCursor beginAt) (CalendarTape.Prefix.histories beginAt path) j
local notation "header" code:arg => (reader).format.windows.header es code seed
local notation "origin" code:arg => v.wideOrigin h width size (header code) π

theorem wide_routed_attempt_on_visit (path : Path slots es base) (j : Fin (es).length)
    {a : Attempt} (onDate : (es).get j=.attempt a) :
    v.electedAttemptAt h width size extent π seed age budget small rowAge floor
      (CalendarTape.Prefix.pathVisitAt path j onDate) (gate path j) := by
  let electedAtVisit := fun z : CalendarTape.Prefix.PathVisit slots es base (.attempt a) =>
    v.electedAttemptAt h width size extent π seed age budget small rowAge floor z (gate path j)
  apply (congrArg electedAtVisit (CalendarTape.Prefix.pathVisitAt_eq_cast path j onDate)).mpr
  exact v.wide_routed_indexed_attempt h width size extent π seed age budget small expanse routeAge floor word path j onDate

/-- The native feed cut is at the specified original ordinal, including when
the same feed label occurs again at a different ordinal. -/
theorem wide_routed_feed_at_date (path : Path slots es base) (j : Fin (es).length)
    {b : Boundary} (day : (es).get j=.feed b) :
    let z:=cast (congrArg (fun f=>CalendarTape.Prefix.PathVisit slots es base f) day) (visit path j)
    ∃ (key : Bits (CalendarTape.bits slots es)) (past : List Event)
      (_ : Calendar.Slot C (origin key) (.feed b) past z.tail z.mem),
      past.length=j.val ∧ StockBound.state C (origin key) j.val=z.mem ∧
      StockBound.state C (origin key) (j.val+1)=after C (.feed b) z.mem ∧
      v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits (header key))
        feeds budget small v.maxBits j b day (gate path j) := by
  let z:=cast (congrArg (fun f=>CalendarTape.Prefix.PathVisit slots es base f) day) (visit path j)
  have elected := v.wide_routed_indexed_feed h width size extent π seed age budget small expanse routeAge floor word path j day
  rcases elected with ⟨key,past,cut,i,tag,ord,before,afterDay,receipt⟩
  have time:=(v.indexedFundedDate_at h width size extent π seed age budget small path j day).2.2
  change (es).length-z.tail.length=j.val+1 at time
  have mesh_eq : (C).mesh = v.mesh := rfl
  have len : (es).length=past.length+(z.tail.length+1) := by
    simpa only [z,mesh_eq,List.length_append,List.length_cons] using congrArg List.length cut.events
  have same : i=j:=Fin.ext (by omega)
  subst i
  exact ⟨key,past,cut,ord.symm,before,afterDay,receipt⟩

private theorem transferIndexedPresentation {K : ℕ} {F : Type} {sourceWidth targetWidth U V : Widths K}
    {initial : SiteMatrix (State sourceWidth) (State targetWidth) F} {selected : SiteMatrix (State U) (State V) F}
    (predicate : ∀ {left right : Widths K}, SiteMatrix (State left) (State right) F → Prop)
    (same : CalendarTape.Prefix.IndexedOperator initial selected) (initialFact : predicate initial) :
    predicate selected := by
  obtain ⟨startEq,endEq,operatorEq⟩ := same
  subst U
  subst V
  subst selected
  exact initialFact


private theorem selected_feed_operand {e : Event} {b : Boundary} (day : e=.feed b)
    (z : CalendarTape.Prefix.PathVisit slots es base e) {U V : Widths (siteLast h D k+1)}
    (stageMatrix : SiteMatrix (State U) (State V) F)
    (same : CalendarTape.Prefix.IndexedOperator ((cal).operator π z.prior z.choice) stageMatrix) :
    let z':=cast (congrArg (fun f=>CalendarTape.Prefix.PathVisit slots es base f) day) z
    let J:=v.wide_funded_date_with h width size extent π seed age budget small z'.prior z'.choice z'.future
    v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits (header J.code))
      feeds budget small v.maxBits J.index b J.index_event stageMatrix := by
  subst e
  let J:=v.wide_funded_date_with h width size extent π seed age budget small z.prior z.choice z.future
  have paid : v.paidBallotHeight≤h := (max_le_iff.mp sub).1
  have causal := (max_le_iff.mp (max_le_iff.mp paid).1).2
  let predicate {left right : Widths (siteLast h D k+1)} (op : SiteMatrix (State left) (State right) F) :=
    v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits (header J.code))
      feeds budget small v.maxBits J.index b J.index_event op
  have raw := v.cursor_feed_at h width size extent π seed age budget small z.prior z.choice J feeds causal
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let indexing ← Lean.Meta.getFVarFromUserName `same
      let original ← Lean.Meta.getFVarFromUserName `raw
      let pred ← Lean.Meta.getFVarFromUserName `predicate
      let typ ← Lean.Meta.whnf (← Lean.Meta.inferType indexing)
      unless typ.isAppOf ``CalendarTape.Prefix.IndexedOperator do throwError "expected original indexed matrix"
      let args := typ.getAppArgs
      let result := Lean.mkAppN (Lean.mkConst ``transferIndexedPresentation) (args ++ #[pred,indexing,original])
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal []


/-- The deterministic indexed feed is read on the literal original full
selector, at the input and output dates of this very occurrence. -/
theorem wide_routed_feed_on_path (path : Path slots es base) (j : Fin (es).length)
    {b : Boundary} (day : (es).get j=.feed b) :
    v.wireFeedPresentation h width size extent π.symm
      (v.wideFundedRaw h width v.maxBits (header (CalendarTape.encode slots es base path)))
      feeds budget small v.maxBits j b day (gate path j) := by
  let z:=cast (congrArg (fun f=>CalendarTape.Prefix.PathVisit slots es base f) day) (visit path j)
  let J:=v.wide_funded_date_with h width size extent π seed age budget small z.prior z.choice z.future
  have chosen:=v.indexedFundedDate_at h width size extent π seed age budget small path j day
  have atCode : J.code=CalendarTape.encode slots es base path := chosen.1
  have atDay : J.index=j := Fin.ext chosen.2.1
  have operand:=v.selected_feed_operand h width size extent π seed age budget small expanse routeAge floor word
    day (visit path j) (gate path j) (CalendarTape.Prefix.indexed_operator ((cal).width π) ((cal).operator π) path j)
  change v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits (header J.code))
    feeds budget small v.maxBits J.index b J.index_event (gate path j) at operand
  have transfer {src dst : Bits (CalendarTape.bits slots es)} {i n : Fin (es).length}
      (codeEq : src=dst) (timeEq : i=n) (t₀ : (es).get i=.feed b) (t₁ : (es).get n=.feed b)
      (ok : v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits (header src))
        feeds budget small v.maxBits i b t₀ (gate path j)) :
      v.wireFeedPresentation h width size extent π.symm (v.wideFundedRaw h width v.maxBits (header dst))
        feeds budget small v.maxBits n b t₁ (gate path j) := by
    subst dst
    subst n
    exact ok
  exact transfer atCode atDay J.index_event day operand

end Feed

variable {a : Attempt} (z : CalendarTape.Prefix.PathVisit slots es base (.attempt a))
local notation "H" => v.wide_funded_date h width size extent π seed age budget small z.prior z.choice
local notation "J" => v.wide_funded_date_with h width size extent π seed age budget small z.prior z.choice z.future
local notation "ref" => v.wide_reference_date h width size extent π seed age budget small z.prior

/-- Read the very same paid amounts, spill weights and active incidences on
the archived tape completed by the original path's remaining ballots. -/
abbrev electedAttemptReplay (expanse : v.wideFundedSize h width v.maxBits≤ size)
    (ledgerHeight : v.wideDatedLedgerHeight≤h) (paidAge : v.paidBallotHeight≤h) :=
  And.intro ((H).middle_replay J expanse ledgerHeight paidAge (0:Word w))
    (And.intro ((H).middle_mount J extent paidAge)
      (And.intro ((H).spill_replay J) (fun (e : Fin (P).catalogue.rows) (live : 0<(H).afterPaid e)=>
        (H).middle_ends J extent paidAge e live)))

/-- The elected reference packet's physical operands on the original, fully
continued visit. The result retains the measured histogram and code readouts. -/
abbrev electedAttemptPacketReads (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width) :=
  (ref).2.packet_reads_on J extent tall floor

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
