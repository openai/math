import OAI.Computability.MultitapeWeakETH.HistoryChildBank
import OAI.Computability.MultitapeWeakETH.HistoryStageDispatch
import OAI.Computability.MultitapeWeakETH.ShrinkKernelReader
import OAI.Computability.MultitapeWeakETH.HistoryRefreshQuery
import OAI.Computability.MultitapeWeakETH.SourceReader
import OAI.Computability.MultitapeWeakETH.WitnessWalk

/-! # A tape visitor for the three chronological witness roles -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code WitnessWalk CNFNetwork.SwitchFactor
open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram

abbrev Kernel := ShrinkReadQuery → Option (List Tally × Bits.Word)
abbrev NodeQuery := (HistorySite × Bits.Word) × Bits.Word
abbrev VisitContext := LeafSyntax.Query × WriteBytes

/-- Each child inherits the preceding layer and its own ordered packet. -/
def childJobs (q : Tally × (List Tally × List Bits.Word)) : List Job :=
  (zipFair [] [] q.2).map fun p => ((q.1,p.1),p.2)

theorem childJobs_poly : Poly childJobs :=
  (Easy.fst.poly.pair (Easy.snd.poly.compose (easy_zip [] []).poly)).compose
    (Poly.push [] ([],[]) (show Poly (fun p : Tally × (Tally × Bits.Word) => ((p.1,p.2.1),p.2.2)) by fun_prop))

theorem childJobs_ordered {I : Type} (level : Tally) (ids : I → Tally) (packets : I → Bits.Word) (xs : List I) :
    childJobs (level,xs.map ids,xs.map packets) = xs.map (fun i => ((level,ids i),packets i)) := by
  unfold childJobs
  rw [fair,List.map_map]
  rfl

/-- A refresh has one child and consumes no further private bits after its packet. -/
def refreshKernel (run : RefreshQuery → Option (List Tally)) (q : ShrinkReadQuery) : Option (List Tally × Bits.Word) :=
  (run (q.1.1,q.1.2.1.2.headD [],q.1.2.2)).bind fun ls => some (ls,q.2)

theorem refreshKernel_poly {run : RefreshQuery → Option (List Tally)} (hr : Poly run) : Poly (refreshKernel run) := by
  have first : Poly (fun xs : List Bits.Word => xs.headD []) := by
    convert (Easy.listCase (X:=Bits.Word) [] Easy.fst).poly using 1
    funext xs; cases xs <;> rfl
  have field := (show Poly (fun q : ShrinkReadQuery => q.1.2.1.2) by fun_prop).compose first
  have args := (show Poly (fun q : ShrinkReadQuery => q.1.1) by fun_prop).pair
    (field.pair (show Poly (fun q : ShrinkReadQuery => q.1.2.2) by fun_prop))
  exact bind_poly [] (args.compose hr) ((Easy.snd.pair (Easy.fst.compose Easy.snd)).compose Easy.some).poly

private def atNode (kernel : Kernel) (q : NodeQuery × ChildResult) : Option Answer :=
  let jobs := childJobs (q.1.1.1.1.2,q.2.1.1,q.2.1.2.2)
  (kernel ((q.1.1.1,q.2.1.2,q.1.1.2),q.2.2)).bind fun a => some ((jobs,a.2),a.1)

private theorem atNode_poly {kernel : Kernel} (hk : Poly kernel) : Poly (atNode kernel) := by
  let X := NodeQuery × ChildResult
  have jobs := (show Poly (fun q : X => (q.1.1.1.1.2,q.2.1.1,q.2.1.2.2)) by dsimp only [X]; fun_prop).compose childJobs_poly
  have key := (show Poly (fun q : X => ((q.1.1.1,q.2.1.2,q.1.1.2),q.2.2)) by dsimp only [X]; fun_prop).compose hk
  exact bind_poly ([],[]) key ((((Easy.fst.poly.compose jobs).pair (Easy.snd.compose Easy.snd).poly).pair
    (Easy.snd.compose Easy.fst).poly).compose Easy.some.poly)

/-- Read child packets before invoking the stage-specific kernel on the remaining suffix. -/
def passVisit (children : HistorySite × Bits.Word → Option ChildResult) (kernel : Kernel) (q : NodeQuery) :=
  (children (q.1.1,q.2)).bind fun a => atNode kernel (q,a)

theorem passVisit_poly {children : HistorySite × Bits.Word → Option ChildResult} {kernel : Kernel}
    (hc : Poly children) (hk : Poly kernel) : Poly (passVisit children kernel) :=
  bind_poly default (((Easy.fst.compose Easy.fst).pair Easy.snd).poly.compose hc) (atNode_poly hk)

theorem passVisit_iff (children : HistorySite × Bits.Word → Option ChildResult) (kernel : Kernel)
    (q : NodeQuery) (jobs : List Job) (tail : Bits.Word) (labels : List Tally) :
    passVisit children kernel q = some ((jobs,tail),labels) ↔
      ∃ ids bank rest, children (q.1.1,q.2) = some ((ids,bank),rest) ∧
        kernel ((q.1.1,bank,q.1.2),rest) = some (labels,tail) ∧
        jobs = childJobs (q.1.1.1.2,ids,bank.2) := by
  simp only [passVisit,atNode,Option.bind_eq_some_iff,Option.some.injEq,Prod.mk.injEq,Prod.exists]
  grind

private def earlier (q : (VisitContext × Job) × Bits.Word) : NodeQuery :=
  (((((q.1.1.1.1,q.1.1.2),q.1.2.1.1.tail),q.1.2.1.2),q.1.2.2),q.2)

private def leaf (K : ℕ) (q : (VisitContext × Job) × Bits.Word) : Option Answer :=
  bif sourceCheck K (q.1.1.1,q.1.2.1.2,q.1.2.2) then some (([],q.2),[]) else none

/-- Layer zero queries the encoded formula. A successor layer reads the previous
pass and selects its kernel by the pass index modulo the schedule period. -/
def visitor {stages : ℕ} (K : ℕ) (children : HistorySite × Bits.Word → Option ChildResult)
    (shrinking : Fin stages → Kernel) (refresh : RefreshQuery → Option (List Tally)) : Visit VisitContext := fun q =>
  bif q.1.2.1.1.isEmpty then leaf K q else
    passVisit children (fun x => dispatch shrinking (refreshKernel refresh) (x.1.1.1.2,x)) (earlier q)

theorem visitor_poly {stages : ℕ} (K : ℕ) {children : HistorySite × Bits.Word → Option ChildResult}
    {shrinking : Fin stages → Kernel} {refresh : RefreshQuery → Option (List Tally)}
    (hc : Poly children) (hs : ∀ i, Poly (shrinking i)) (hr : Poly refresh) :
    Poly (visitor K children shrinking refresh) := by
  let X := (VisitContext × Job) × Bits.Word
  have empty : Poly (fun t : Tally => t.isEmpty) := by
    convert (Easy.listCase (X:=Unit) true (Easy.const false)).poly using 1
    funext t; cases t <;> rfl
  have tl : Poly (fun t : Tally => t.tail) := by
    convert (Easy.listCase (X:=Unit) [] Easy.snd).poly using 1
    funext t; cases t <;> rfl
  have level : Poly (fun q : X => q.1.2.1.1) := by clear hs; dsimp only [X]; fun_prop
  have prev : Poly earlier := by clear hs; unfold earlier; fun_prop (disch := assumption)
  have args : Poly (fun q : X => (q.1.1.1,q.1.2.1.2,q.1.2.2)) := by clear hs; dsimp only [X]; fun_prop
  have src : Poly (leaf K) := Poly.choose (args.compose (sourceCheck_poly K))
    ((((Code.Poly.const []).pair Easy.snd.poly).pair (Code.Poly.const [])).compose Easy.some.poly) (Code.Poly.const none)
  have kern := (show Poly (fun x : ShrinkReadQuery => (x.1.1.1.2,x)) by clear hs; fun_prop).compose
    (dispatch_poly hs (refreshKernel_poly hr))
  exact Poly.choose (level.compose empty) src (prev.compose (passVisit_poly hc kern))

end OAI.Computability.MultitapeWeakETH.NativeGrid
