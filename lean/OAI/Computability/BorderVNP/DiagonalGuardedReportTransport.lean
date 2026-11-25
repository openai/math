import OAI.Computability.BorderVNP.DiagonalAssignedNativeCompletion

/-! # Report passing and native finish receipts indexed by the received rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM CompactMachine CellMacro.Generator
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader DiagonalTallyCellReports
open BorderVNP.Cube
open scoped Classical BigOperators

/-- The common layout and typed cell lists identify every pre-call passing
proof with the corresponding proof for the assigned row. -/
theorem passing_of_same_rows {T n w : ℕ} {a b : Fin T → ReportLayout}
    {xs : ∀ t,List (AssignedCell (a t))} {ys : ∀ t,List (AssignedCell (b t))}
    (sameLayout : a=b) (sameRows : HEq xs ys)
    (pass : ∀ t c, c∈ys t → c.Passing w n) : ∀ t c, c∈xs t → c.Passing w n := by
  subst b
  obtain rfl := eq_of_heq sameRows
  exact pass

/-- The concrete prepared candidate installed these typed rows and their
report layout. Both identities are definitional on the genuine prepared
source, including the layout of each receiving team. -/
def UncheckedCandidate.UsesRows {axes box lanes selectors symbols n w teams dim width : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (X : UncheckedCandidate id gen n w teams dim width) {chart : Fin teams → ReportLayout}
    (cells : ∀ u, List (AssignedCell (chart u))) : Prop :=
  X.layout=chart ∧ HEq X.assigned cells

/-- The actual selected-operand return for every subtotal proposal on one
given original assignment, including the preserved low memory and the
placement of the processor's startup arena. -/
def UncheckedCandidate.ReturnedFinish {axes box lanes selectors symbols n w teams dim width reserve groups cap : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (X : UncheckedCandidate id gen n w teams dim width) (p : PositiveFields reserve axes groups cap teams dim width)
    (rows : Fin teams → Fin dim → ℕ) (layout : Fin teams → SignedTaskArena.Layout) (arena : Fin teams → StartupArena) : Prop :=
  ∀ (pass : ∀ t c, c ∈ X.assigned t → c.Passing w n) raw t, let rr := canonicalReports X.assigned pass
    let team := X.team rr raw t
    let a := (X.candidate rr raw).1 t
    let mac := install gen n team.routines
    ∃ receipt : PositiveFields.FinishInput t rows width team.pub mac (cellBank team.pub mac a.2.val.2.1 a.2.val.2.2)
      a.2.val.2.2 (p.withSubtotals raw).tallyWords,
      receipt.post=(layout t).after ∧ (∀ j<(layout t).after.start, j≠(team.pub 0).val+35 →
        receipt.selected j=a.2.val.2.2 j) ∧ (team.pub 0).val=(arena t).frame ∧ (arena t).next≤(layout t).cube.header.header


/-- Choose each actual selected-operand return once and retain its protected
low words together with the checked numerical row it reported. -/
theorem UncheckedCandidate.completeReturned {axes box lanes selectors symbols n w teams dim width reserve groups cap : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (X : UncheckedCandidate id gen n w teams dim width) (p : PositiveFields reserve axes groups cap teams dim width)
    (rows : Fin teams → Fin dim → ℕ) (layout : Fin teams → SignedTaskArena.Layout) (arena : Fin teams → StartupArena)
    (pass : ∀ t c, c ∈ X.assigned t → c.Passing w n) (received : X.ReturnedFinish p rows layout arena)
    (room : width ≤ w) (rowBounds : ∀ t c, rows t c < 2^width) (sumBounds : ∀ c, ∑ t,rows t c < 2^w) :
    ∃ H : X.Completion p, H.rows=rows ∧ ∀ raw t,H.Protected X raw t (layout t) (arena t) := by
  choose start evidence using received pass
  let H : X.Completion p := ⟨pass,rows,start,room,rowBounds,sumBounds⟩
  refine ⟨H,rfl,?_⟩
  intro raw t
  obtain ⟨post,retained,frame,place⟩ := evidence raw t
  exact ⟨post,retained,frame,place⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
