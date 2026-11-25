import OAI.Computability.BorderVNP.DiagonalTallyReportChoiceCover
import OAI.Computability.BorderVNP.DiagonalTallyReportBatchCost
import OAI.Computability.BorderVNP.DiagonalNativeSequence

/-! # The finite report tape of a native owned-cell traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM

variable {w : ℕ} {l : ReportLayout} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Chronological gadget count digits and expanded use flags on the actual owned cells. -/
abbrev ReportTape (cs : List (ReportCell l)) := Fin (reportBits cs).length → Bool

/-- Decode only the finite stream consumed by the stage into the physically ordered cells. -/
def cellsOfTape (cs : List (ReportCell l)) (tape : ReportTape cs) :=
  tapeCells (fun i => if h : i < (reportBits cs).length then tape ⟨i,h⟩ else false) 0 cs

@[simp] theorem cellsOfTape_bits (cs : List (ReportCell l)) (tape : ReportTape cs) :
    reportBits (cellsOfTape cs tape)=List.ofFn tape := by
  rw [cellsOfTape,tapeCells_bits]
  simp [reportSlice]

/-- Physical conditions at the entry of the compiled stage. The recursive input
condition concerns only actual addresses, stored literals and numerical room. -/
structure PreparedReportInput (pub : Arg → Word w) (m : Memory w) (cs : List (ReportCell l))
    (q : ReportCursor) (description : ℕ) : Prop where
  framePointer : (pub 0).val=l.frame
  first : q.prior=0
  seeded : l.seed q cs.length (readings m)
  frameRoom : l.frame+95<2^w
  controlRoom : l.control+27<2^w
  headerRoom : l.headers+6*cs.length<2^w
  rawRoom : l.fieldWidth+l.bodyCap<2^w
  inputs : ∀ a : ℕ → Bool, cellInputs w description (tapeCells a 0 cs) q l.headers (readings m)

variable {m : Memory w} {cs : List (ReportCell l)} {q : ReportCursor} {description : ℕ}
    (seed : PreparedReportInput pub m cs q description) (mac : TeamOpcode.Macros w 8) (s : Bank w)

/-- Given a tape, the report stage has a native return whose post-memory contains
the exact guess words, sidecar bindings, physical operand arrays and their count. -/
theorem exists_reportReturn (seed : PreparedReportInput pub m cs q description) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (tape : ReportTape cs) :
    ∃ x : Returns prepareCellReports pub mac s m, let rows := cellsOfTape cs tape
      TraceOK x.val.1 (List.ofFn tape) x.val.1.length ∧
      traceCost x.val.1 ≤ prepareSetup.slots+cellTicks rows q+(writeFrame 32 60 61 35).slots ∧
      readings x.val.2.2=Function.update (cellImages rows q (readings m)) (l.frame+35) (cellOperands rows q).length := by
  obtain ⟨es,t,mt,r,tr,cost,image⟩ := prepareCellReports_runs pub mac s m l (cellsOfTape cs tape) q description
    seed.framePointer seed.first (by simpa [cellsOfTape] using seed.seeded) seed.frameRoom seed.controlRoom
    (by simpa [cellsOfTape] using seed.headerRoom) seed.rawRoom (seed.inputs _)
  exact ⟨⟨(es,t,mt),r⟩,by simpa only [cellsOfTape_bits] using tr,cost,image⟩

/-- The equivalence includes every native return, with its own chronological event
sequence, final register bank and shared memory. It works for an empty owner too. -/
noncomputable def reportReturnEquiv (seed : PreparedReportInput pub m cs q description) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) : ReportTape cs ≃ Returns prepareCellReports pub mac s m := by
  apply Equiv.ofBijective (fun tape => (exists_reportReturn seed mac s tape).choose)
  constructor
  · intro a b same
    have ha := (exists_reportReturn seed mac s a).choose_spec.1.2.1
    have hb := (exists_reportReturn seed mac s b).choose_spec.1.2.1
    dsimp only at same
    rw [same] at ha
    exact List.ofFn_injective (ha.symm.trans hb)
  · intro x
    obtain ⟨a,tr,_,_⟩ := prepareCellReports_cover pub mac s m l cs q description
      seed.framePointer seed.first seed.seeded seed.frameRoom seed.controlRoom seed.headerRoom seed.rawRoom
      seed.inputs x.property
    let tape : ReportTape cs := fun i => a i.val
    have bits : reportBits (tapeCells a 0 cs)=List.ofFn tape := by simp [tape,tapeCells_bits,reportSlice]
    let y := (exists_reportReturn seed mac s tape).choose
    have same := prepareCellReports_unique y.property x.property
      ((exists_reportReturn seed mac s tape).choose_spec.1.2.1.trans (tr.2.1.trans bits).symm)
    exact ⟨tape,Subtype.ext (Prod.ext same.1 (Prod.ext same.2.1 same.2.2))⟩

/-- Exact choice stream, charged native work and post-memory of the forward bijection. -/
theorem reportReturnEquiv_spec (tape : ReportTape cs) :
    let x := reportReturnEquiv seed mac s tape
    let rows := cellsOfTape cs tape
    TraceOK x.val.1 (List.ofFn tape) x.val.1.length ∧
      traceCost x.val.1 ≤ prepareSetup.slots+cellTicks rows q+(writeFrame 32 60 61 35).slots ∧
      readings x.val.2.2=Function.update (cellImages rows q (readings m)) (l.frame+35) (cellOperands rows q).length :=
  (exists_reportReturn seed mac s tape).choose_spec

/-- Every finite report path has positive weight, with sparse work charged to its
owned cells, original site metadata, and actual expanded weighted occurrences. -/
theorem reportReturnEquiv_weight_cost (tape : ReportTape cs) :
    let x := reportReturnEquiv seed mac s tape
    let rows := cellsOfTape cs tape
    TeamContraction.pathWeight x.val.1 = 1 ∧
      traceCost x.val.1 ≤ 54+(79+105*l.gadgets+16*(l.gadgets*l.countWidth))*rows.length+
        129*teamOriginal rows*(l.fieldWidth+1)+131*teamWeighted rows := by
  obtain ⟨tr,cost,_⟩ := reportReturnEquiv_spec seed mac s tape
  refine ⟨?_,cost.trans (prepare_sparse_charge ..)⟩
  apply List.prod_eq_one
  intro v hv
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
  simp [(tr.2.2 e he),TeamRAM.Sign.value]

/-- Recover the unique finite tape directly from the chronological choices of
any native return, including one obtained by cutting a longer evaluator trace. -/
theorem reportReturnEquiv_recover (x : Returns prepareCellReports pub mac s m) :
    x.val.1.flatMap TeamRAM.Event.choices=List.ofFn ((reportReturnEquiv seed mac s).symm x) := by
  have result := (reportReturnEquiv_spec seed mac s ((reportReturnEquiv seed mac s).symm x)).1.2.1
  simpa only [Equiv.apply_symm_apply] using result

/-- Finiteness of actual report paths follows from their prescribed finite choice count. -/
noncomputable abbrev reportReturnsFintype (seed : PreparedReportInput pub m cs q description)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) : Fintype (Returns prepareCellReports pub mac s m) :=
  Fintype.ofEquiv _ (reportReturnEquiv seed mac s)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
