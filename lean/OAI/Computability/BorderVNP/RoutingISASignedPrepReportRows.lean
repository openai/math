import OAI.Computability.BorderVNP.RoutingISASignedPrepReports

/-! # Reindexing report returns by the actual cell count and use fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

private theorem redecodeBundles (a b : ℕ → Bool) (bs : List ReportBundle) (p r : ℕ) :
    tapeBundles a p (tapeBundles b r bs)=tapeBundles a p bs := by
  induction bs generalizing p r with
  | nil => rfl
  | cons c cs ih => simp [tapeBundles,ReportBundle.withTape,ReportBundle.useCount,ih]

private theorem redecodeCell {l : ReportLayout} (a b : ℕ → Bool) (c : ReportCell l) (p r : ℕ) :
    (c.withTape b r).withTape a p=c.withTape a p := by simp [ReportCell.withTape,redecodeBundles]

private theorem redecode {l : ReportLayout} (a b : ℕ → Bool) (cs : List (ReportCell l)) (p r : ℕ) :
    tapeCells a p (tapeCells b r cs)=tapeCells a p cs := by
  induction cs generalizing p r with
  | nil => rfl
  | cons c cs ih => simp [tapeCells,redecodeCell,ih]

private theorem recoverBundles (a : ℕ → Bool) (bs : List ReportBundle) (p : ℕ)
    (eqBits : (tapeBundles a p bs).flatMap (fun b => List.ofFn b.uses)=bs.flatMap (fun b => List.ofFn b.uses)) :
    tapeBundles a p bs=bs := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    simp only [tapeBundles,List.flatMap_cons] at eqBits ⊢
    have split := List.append_inj eqBits (by simp [ReportBundle.withTape])
    have uses := List.ofFn_injective split.1
    have same : b.withTape a p=b := by
      cases b
      simp only [ReportBundle.withTape,ReportBundle.mk.injEq,true_and]
      exact heq_of_eq uses
    rw [same,ih _ split.2]

private theorem countFields_injective {n d : ℕ} :
    Function.Injective (fun f : Fin n → Fin d → Bool => (List.ofFn fun i => List.ofFn (f i)).flatten) := by
  induction n with
  | zero => intro f g _; funext i; exact i.elim0
  | succ n ih =>
    intro f g h
    simp only [List.ofFn_succ,List.flatten_cons] at h
    obtain ⟨head,tail⟩ := List.append_inj h (by simp)
    have same := ih tail
    funext i
    exact Fin.cases (List.ofFn_injective head) (fun j => congrFun same j) i

private theorem recoverCell {l : ReportLayout} (a : ℕ → Bool) (c : ReportCell l) (p : ℕ)
    (eqBits : (c.withTape a p).bits=c.bits) : c.withTape a p=c := by
  unfold ReportCell.bits at eqBits
  have split := List.append_inj eqBits (by simp [List.length_flatten,List.map_ofFn,Function.comp_def])
  have counts := countFields_injective split.1
  have bundles := recoverBundles a c.bundles _ split.2
  cases c
  simp only [ReportCell.withTape,ReportCell.mk.injEq,true_and] at counts ⊢
  exact ⟨bundles,counts⟩

private theorem recover {l : ReportLayout} (a : ℕ → Bool) (cs : List (ReportCell l)) (p : ℕ)
    (eqBits : reportBits (tapeCells a p cs)=reportBits cs) : tapeCells a p cs=cs := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    change (c.withTape a p).bits ++ reportBits (tapeCells a (p+c.tailWidth) cs)=c.bits ++ reportBits cs at eqBits
    obtain ⟨head,tail⟩ := List.append_inj eqBits (by simp only [ReportCell.bits_length,ReportCell.withTape_tailWidth])
    exact congrArg₂ List.cons (recoverCell a c p head) (ih _ tail)

/-- Clear the sampled gadget digits and use flags while retaining the ordered physical
cell headers, bundle geometry, original private factor strings and marked positions. -/
def eraseReportBits {l : ReportLayout} (cs : List (ReportCell l)) := tapeCells (fun _ => false) 0 cs

/-- Exactly the count and use assignments to this list of actual received cells. -/
abbrev ReportAssignments {l : ReportLayout} (cs : List (ReportCell l)) :=
  {rows : List (ReportCell l) // eraseReportBits rows=eraseReportBits cs}

/-- The native stream is bijective with all count-digit and expanded use fields on the
given immutable cells. There is one assignment per bit sequence even for zero-width
counts, unmarked bundles, empty site lists and an owner with no cells. -/
noncomputable def reportAssignmentEquiv {l : ReportLayout} (cs : List (ReportCell l)) :
    ReportTape cs ≃ ReportAssignments cs := by
  apply Equiv.ofBijective (fun tape => ⟨cellsOfTape cs tape,redecode ..⟩)
  constructor
  · intro a b eq
    have bits := congrArg (fun r : ReportAssignments cs => reportBits r.val) eq
    exact List.ofFn_injective (by simpa only [cellsOfTape_bits] using bits)
  · intro rows
    have len := congrArg (fun xs => (reportBits xs).length) rows.property
    simp only [eraseReportBits,tapeCells_bits,reportSlice,List.length_ofFn] at len
    let tape : ReportTape cs := fun i => (reportBits rows.val)[i.val]'(i.isLt.trans_eq len.symm)
    have bits : List.ofFn tape=reportBits rows.val := by
      apply List.ext_getElem
      · simpa using len.symm
      · intro i hi hj; simp [tape]
    let a : ℕ → Bool := fun i => if h : i<(reportBits cs).length then tape ⟨i,h⟩ else false
    have aligned : cellsOfTape cs tape=tapeCells a 0 rows.val := by
      change tapeCells a 0 cs=_
      rw [← redecode a (fun _ => false) cs 0 0]
      change tapeCells a 0 (eraseReportBits cs)=_
      exact (congrArg (tapeCells a 0) rows.property.symm).trans (redecode ..)
    have restored := recover a rows.val 0 (by rw [←aligned,cellsOfTape_bits,bits])
    exact ⟨tape,Subtype.ext (aligned.trans restored)⟩

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM

variable {w description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w}

/-- Reindex the actual program return by its chronological, physically addressed report
cells. This keeps the supplied fields in the same representation used by tallying. -/
noncomputable def assignedReportReturnEquiv (seed : PreparedReportInput pub m cs q description)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) :
    ReportAssignments cs ≃ Returns prepareCellReports pub mac s m :=
  (reportAssignmentEquiv cs).symm.trans (reportReturnEquiv seed mac s)

/-- The post-memory and chronological choice stream for an assignment use its own
gadget bits and marked-copy flags on the original rows. -/
theorem assignedReportReturnEquiv_spec (seed : PreparedReportInput pub m cs q description)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (rows : ReportAssignments cs) :
    let x := assignedReportReturnEquiv seed mac s rows
    TraceOK x.val.1 (reportBits rows.val) x.val.1.length ∧
      readings x.val.2.2=Function.update (cellImages rows.val q (readings m))
        (l.frame+35) (cellOperands rows.val q).length := by
  let tape := (reportAssignmentEquiv cs).symm rows
  have same : cellsOfTape cs tape=rows.val := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have bits := (cellsOfTape_bits cs tape).symm
  obtain ⟨tr,_,image⟩ := reportReturnEquiv_spec seed mac s tape
  rw [bits,same] at tr
  rw [same] at image
  exact ⟨tr,image⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
