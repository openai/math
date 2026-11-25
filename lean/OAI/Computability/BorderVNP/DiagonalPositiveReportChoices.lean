import OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows
import OAI.Computability.BorderVNP.DiagonalNativeReportFiber

/-! # Canonical physically received report fields and residual native choices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CellSparse DiagonalResidueRAM
open scoped Classical

variable {w order : ℕ} {l : ReportLayout} (ss : List (AssignedCell l))
    (ok : ∀ v ∈ ss, v.Passing w order)

/-- All received counts and use flags and all residual private choices at the
fixed original assignments. The erased geometry is the received geometry. -/
abbrev ReportChoice (w order : ℕ) (ss : List (AssignedCell l)) :=
  {v : ReportAssignments (ss.map AssignedCell.report) × List (List Bool × Bool) //
    BatchReturns w order ss v.1.val v.2}

include ok in
/-- There is exactly one passing physically addressed assignment, including
the residual choice tapes of all its cells. Its native report stream consists
of the canonical count and use spellings, with positive signs throughout. -/
theorem reportChoice_unique : ∃ z : ReportChoice w order ss,
    reportBits z.val.1.val=ss.flatMap AssignedCell.spelling ∧
      (∀ t∈z.val.2, t.2=false) ∧ ∀ y : ReportChoice w order ss,y=z := by
  let cs := ss.map AssignedCell.report
  let spell := ss.flatMap AssignedCell.spelling
  have len := batch_spelling_length w order ss ok
  let tape : ReportTape cs := fun i => spell[i.val]'(i.isLt.trans_eq len.symm)
  have spelling : List.ofFn tape=spell := by
    apply List.ext_getElem
    · exact List.length_ofFn.trans len.symm
    · intro j hj _; simp [tape]
  obtain ⟨aux,haux⟩ := batch_native w order ss ok
  let rows := reportAssignmentEquiv cs tape
  let ret := aux.map fun u => (u,false)
  have actual (a : ReportTape cs) (r : List (List Bool × Bool)) :
      BatchReturns w order ss (cellsOfTape cs a) r ↔
      reportBits (cellsOfTape cs a)=spell ∧ r=ret :=
    haux (fun i => if h : i < (reportBits cs).length then a ⟨i,h⟩ else false) 0 r
  have image : reportBits rows.val=spell := (cellsOfTape_bits cs tape).trans spelling
  let z : ReportChoice w order ss := ⟨(rows,ret),(actual tape ret).mpr ⟨image,rfl⟩⟩
  refine ⟨z,image,?_,?_⟩
  · intro t ht
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht
    rfl
  · intro y
    let b := (reportAssignmentEquiv cs).symm y.val.1
    have rowEq : reportAssignmentEquiv cs b = y.val.1 := Equiv.apply_symm_apply ..
    have rowVal : cellsOfTape cs b = y.val.1.val := congrArg Subtype.val rowEq
    have witnessed := (actual b y.val.2).mp (rowVal ▸ y.property)
    have same : b=tape := List.ofFn_injective ((cellsOfTape_bits cs b).symm.trans (witnessed.1.trans spelling.symm))
    exact Subtype.ext (Prod.ext (rowEq.symm.trans (congrArg (reportAssignmentEquiv cs) same)) witnessed.2)

include ok in
/-- Transport the sole checked report assignment into the actual report-stage
return. The chronological choices and every resulting memory word are retained. -/
theorem reportChoice_native {pub : Arg → Word w} {m : Memory w} {q : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub m (ss.map AssignedCell.report) q description)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (y : ReportChoice w order ss) :
    let a := assignedReportReturnEquiv seed mac s y.val.1
    TraceOK a.val.1 (ss.flatMap AssignedCell.spelling) a.val.1.length ∧
      readings a.val.2.2=Function.update (cellImages y.val.1.val q (readings m))
        (l.frame+35) (cellOperands y.val.1.val q).length ∧ ∀ t∈y.val.2,t.2=false := by
  obtain ⟨z,bits,sign,unique⟩ := reportChoice_unique ss ok
  rw [unique y]
  obtain ⟨trace,image⟩ := assignedReportReturnEquiv_spec seed mac s z.val.1
  exact ⟨bits ▸ trace,image,sign⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
