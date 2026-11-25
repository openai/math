import OAI.Computability.BorderVNP.DiagonalReportBatchFiber
import OAI.Computability.BorderVNP.DiagonalTallyReportChoiceCover

/-! # The genuine all-team report preparation fiber for fixed passing cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA VPVNP.BurstRAM DiagonalResidueRAM CellSparse
open scoped Classical

/-- The actual returning report prefix and the residual native cell choices.
The full native memory and registers are included in the uniqueness claim. -/
structure PreparedReturn (w : ℕ) where
  /-- Chronological events of the native report-preparation run. -/
  events : List (TeamRAM.Event w)
  /-- Register bank when report preparation returns. -/
  registers : Bank w
  /-- Memory when report preparation returns. -/
  memory : Memory w
  /-- Residual choice tape and sign bit of each private cell call, in report order. -/
  cells : List (List Bool × Bool)

/-- Inputs and source arena bounds at the report-guessing instruction. -/
structure ReportSetup {l : ReportLayout} {w : ℕ} (pub : Arg → Word w) (m : Memory w) (q : ReportCursor)
    (description : ℕ) (ss : List (AssignedCell l)) : Prop where
  framePointer : (pub 0).val=l.frame
  priorZero : q.prior=0
  seeded : l.seed q ss.length (readings m)
  frameRoom : l.frame+95<2^w
  controlRoom : l.control+27<2^w
  headersRoom : l.headers+6*ss.length<2^w
  rawRoom : l.fieldWidth+l.bodyCap<2^w
  arena : ∀ a : ℕ → Bool, cellInputs w description (tapeCells a 0 (ss.map AssignedCell.report)) q l.headers (readings m)

/-- Successful native report producer and successful fixed-payload cell
returns, using the original event choice stream at the actual site cursor. -/
def PreparedReturn.Passing {l : ReportLayout} {w : ℕ} (p : PreparedReturn w)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (order : ℕ) (ss : List (AssignedCell l)) : Prop :=
  Runs pub mac prepareCellReports s m p.events p.registers p.memory ∧
    BatchReturns w order ss (tapeCells (lookup (p.events.flatMap TeamRAM.Event.choices)) 0
      (ss.map AssignedCell.report)) p.cells

private theorem slice_read (xs : List Bool) {n : ℕ} (hn : xs.length=n) : reportSlice (lookup xs) 0 n=xs := by
  subst n
  apply List.ext_getElem
  · simp [reportSlice]
  · intro i hi hi'
    simp [reportSlice,lookup,List.head?_drop]

/-- A fixed passing set of private/core assignments has one report preparation
history, one resulting memory, and one positive native auxiliary tape at each
cell. Every native return is covered by the actual decoder before applying
the private acceptance conditions. -/
theorem prepare_checked_image {l : ReportLayout} {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (q : ReportCursor) (description order : ℕ) (ss : List (AssignedCell l))
    (setup : ReportSetup pub m q description ss) (ok : ∀ v ∈ ss, v.Passing w order) :
    ∃ p : PreparedReturn w, p.Passing pub mac s m order ss ∧
      TraceOK p.events (ss.flatMap AssignedCell.spelling) p.events.length ∧
      (∀ ret ∈ p.cells, ret.2=false) ∧
      (let rows := tapeCells (lookup (ss.flatMap AssignedCell.spelling)) 0 (ss.map AssignedCell.report)
       traceCost p.events ≤ prepareSetup.slots+cellTicks rows q+(writeFrame 32 60 61 35).slots ∧
       readings p.memory = Function.update (cellImages rows q (readings m)) (l.frame+35) (cellOperands rows q).length) ∧
      (∀ p' : PreparedReturn w, p'.Passing pub mac s m order ss → p'=p) := by
  let cs := ss.map AssignedCell.report
  let expected := ss.flatMap AssignedCell.spelling
  let a := lookup expected
  let rows := tapeCells a 0 cs
  have n := batch_spelling_length w order ss ok
  have eb : reportBits rows=expected := (tapeCells_bits a 0 cs).trans (slice_read expected n)
  obtain ⟨aux,haux⟩ := batch_native w order ss ok
  let choices := aux.map fun u => (u,false)
  obtain ⟨ev,t,mt,run,trace,cost,img⟩ := prepareCellReports_runs pub mac s m l rows q description setup.framePointer setup.priorZero
    (by simpa only [rows,cs,tapeCells_length,List.length_map] using setup.seeded) setup.frameRoom setup.controlRoom
    (by simpa only [rows,cs,tapeCells_length,List.length_map] using setup.headersRoom) setup.rawRoom (setup.arena a)
  have stream := trace.2.1.trans eb
  let p : PreparedReturn w := ⟨ev,t,mt,choices⟩
  have checkedTrace := trace
  rw [eb] at checkedTrace
  refine ⟨p,⟨run,?_⟩,checkedTrace,?_,⟨cost,img⟩,?_⟩
  · change BatchReturns w order ss (tapeCells (lookup (ev.flatMap TeamRAM.Event.choices)) 0 cs) choices
    rw [stream]
    exact (haux a 0 choices).mpr ⟨eb,rfl⟩
  · intro ret hr
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    rfl
  · rintro ⟨ev',t',mt',choices'⟩ ⟨run',pass'⟩
    obtain ⟨b,covered,_,_⟩ := prepareCellReports_cover pub mac s m l cs q description setup.framePointer setup.priorZero
      (by simpa only [cs,List.length_map] using setup.seeded) setup.frameRoom setup.controlRoom
      (by simpa only [cs,List.length_map] using setup.headersRoom) setup.rawRoom setup.arena run'
    let bs := ev'.flatMap TeamRAM.Event.choices
    have bl : bs.length=(reportBits cs).length := by
      have e := covered.2.1.trans (tapeCells_bits b 0 cs)
      simp only [bs,e,reportSlice,List.length_ofFn]
    have actual := (haux (lookup bs) 0 choices').mp pass'
    have be : bs=expected := (slice_read bs bl).symm.trans
      ((tapeCells_bits (lookup bs) 0 cs).symm.trans actual.1)
    obtain ⟨rfl,rfl,rfl⟩ := prepareCellReports_unique run' run (be.trans stream.symm)
    have er : choices'=choices := actual.2
    subst choices'
    rfl

/-- The true producer and every private call determine a unique path over this
fixed passing team assignment. -/
theorem prepare_checked_unique {l : ReportLayout} {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (q : ReportCursor) (description order : ℕ) (ss : List (AssignedCell l))
    (setup : ReportSetup pub m q description ss) (ok : ∀ v ∈ ss, v.Passing w order) :
    ∃ p : PreparedReturn w, p.Passing pub mac s m order ss ∧
      TraceOK p.events (ss.flatMap AssignedCell.spelling) p.events.length ∧
      (∀ ret ∈ p.cells, ret.2=false) ∧
      (∀ p' : PreparedReturn w, p'.Passing pub mac s m order ss → p'=p) := by
  obtain ⟨p,run,trace,sign,_,unique⟩ := prepare_checked_image pub mac s m q description order ss setup ok
  exact ⟨p,run,trace,sign,unique⟩

/-- The whole team product, at a fixed physical routing/payload assignment.
There is exactly one family of returning native report histories and private
residual tapes, with the canonical bits and positive event signs at each team. -/
theorem all_team_checked_reports {Team : Type*} {w : ℕ} (l : Team → ReportLayout)
    (pub : Team → Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (regs : Team → Bank w) (memory : Team → Memory w) (q : Team → ReportCursor)
    (description : Team → ℕ) (order : ℕ) (ss : ∀ t, List (AssignedCell (l t)))
    (setup : ∀ t, ReportSetup (pub t) (memory t) (q t) (description t) (ss t))
    (ok : ∀ t v, v ∈ ss t → v.Passing w order) :
    ∃! paths : Team → PreparedReturn w, ∀ t, (paths t).Passing (pub t) mac (regs t) (memory t) order (ss t) := by
  choose p hp using fun t => prepare_checked_unique (pub t) mac (regs t) (memory t) (q t) (description t) order
    (ss t) (setup t) (ok t)
  exact ⟨p,fun t => (hp t).1,fun paths passing => funext fun t => (hp t).2.2.2 _ (passing t)⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
