import OAI.ThreeFlat.RAM.PhysicalPrelude
import OAI.ThreeFlat.RAM.PhysicalPreludeMemory
import OAI.ThreeFlat.RAM.PhysicalPreludeBounds
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Executing the six linked preparation phases on the real input tape -/

namespace ThreeFlat.RAM.PhysicalPrelude.Image

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure PhysicalInputPhases BitLayout DescriptorExpr
open scoped Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {w : ℕ} (I : Image F w)
variable (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool) (params : Fin I.parameters → Bool)

/-- Replace only the trace-row generator while retaining both ends of the physical initializer. -/
noncomputable def withTrace (gen : Procedure w) : Procedure w :=
  (((((I.stage.seq I.pack).seq I.params).seq gen).seq I.low).seq I.table)

noncomputable def costWithTrace (rowCost : ℕ) :=
  (6+5*I.sizes.rawCount) + (I.sizes.packedWords*(5*w+6)+6) + (6+5*I.parameters) + rowCost +
    (4+I.firstCell*(2*I.firstWords.binds+4)) + (4+(products (F:=F))*(2*I.productWord.binds+4))

theorem runWithTrace (cap : I.Bounds) (input : Memory w) (raw : I.Raw D x y params input)
    (gen : Procedure w) (rowCost : ℕ)
    (gx : gen.Exec (I.paramMem input) (I.traceMem input) rowCost) :
    (I.withTrace gen).Exec input (I.finalMem D x y input) (I.costWithTrace rowCost) := by
  let target := memory I.H I.field (PhysicalPinsInput.logical D x y) (fun _=>false)
  have st : I.stage.Exec input (I.staged input) _ := Procedure.Spec.exec (copying_spec (w:=w) 0 I.sizes.rawCount I.sizes.scratch (by simpa using cap.raw) cap.scratch
    (Or.inr (by simpa using I.sizes.scratch_after_raw))) input trivial
  have pk : I.pack.Exec (I.staged input) (I.packMem input) _ := Procedure.Spec.exec (packing_spec I.G I.field I.keys (I.sizes.scratch+I.sizes.rawTable) I.sizes.gateBase
    cap.packSafe cap.packEnd) (I.staged input) (I.packInput raw)
  have pp : I.params.Exec (I.packMem input) (I.paramMem input) _ := Procedure.Spec.exec (copying_spec (w:=w) (I.sizes.scratch+I.sizes.rawParams) I.parameters I.sizes.parameterBase
    cap.parameterEnd cap.actualParameters (Or.inl cap.parameterSafe)) (I.packMem input) trivial
  have wl : I.low.Exec (I.traceMem input) (I.lowMem D x y input) _ := Procedure.Spec.exec (writing_spec I.firstWords blank 0 I.firstCell (by simpa using cap.first)
    (fun m => m=I.traceMem input) target (by
      rintro m rfl q current _ hq keep
      apply PhysicalPinsInput.low_eval I.H I.field D x y I.sizes.scratch _ current q (by simpa using hq)
        cap.first cap.rawInputs
      intro j hj
      exact (keep _ (Or.inr (by simpa using cap.lowScratch.trans (Nat.le_add_right _ j)))).trans
        (I.lowInput raw j hj))) (I.traceMem input) rfl
  have wf : I.table.Exec (I.lowMem D x y input) (I.finalMem D x y input) _ := Procedure.Spec.exec (writing_spec I.productWord blank I.firstProduct (products (F:=F)) cap.footprint
    (fun _ => True) target (by
      intro m _ q current lo hi _
      exact PhysicalFieldTable.atAddress_memory I.H I.field (PhysicalPinsInput.logical D x y)
        (fun _=>false) (fun _=>0) _ current (fun _=>q) _ _ q.val lo hi cap.footprint.le
        (by simp) (Fin.cast_val_eq_self q).symm)) (I.lowMem D x y input) trivial
  unfold withTrace costWithTrace
  intro P R K
  exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then
    (Procedure.Exec.then (Procedure.Exec.then st pk) pp) gx) wl) wf

theorem run (fit : I.Fits) (input : Memory w) (raw : I.Raw D x y params input) :
    I.procedure.Exec input (I.finalMem D x y input) I.cost := by
  have cap := I.bounds fit
  apply I.runWithTrace D x y params cap input raw I.trace
    (4+11*I.X.cells*(2*(FixedTraceProgram.program w).binds+4))
  exact Procedure.Spec.exec (writing_spec (FixedTraceProgram.program w) I.Xdata I.sizes.templateBase (11*I.X.cells)
    cap.traceEnd (fun m => m=I.paramMem input) (PhysicalTraceSource.rowWord I.X I.field I.sizes.templateBase) (by
      intro m hm
      subst m
      exact PhysicalTraceSource.row_correct I.G I.field I.keys I.input I.sizes.templateBase I.sizes.gateBase
        I.sizes.portBase I.Xdata (I.paramMem input) I.Xdata_public (I.traceGate input) (I.tracePort input)
        le_rfl (by exact Nat.le_add_right _ _) cap.traceEnd cap.traceGate cap.tracePorts
        fit.ruleFits fit.ports fit.addresses fit.localCells fit.records)) (I.paramMem input) rfl
/-- No input-dependent facts are put into the native table. -/
theorem prepares (fit : I.Fits) :
    I.procedure.Spec (I.Raw D x y params) (fun _ m => I.Ready D x y params m) I.cost :=
  Procedure.spec_of_exec (f:=I.finalMem D x y) (fun m h => I.run D x y params fit m h)
    (fun _ h => I.finalReady h)


end ThreeFlat.RAM.PhysicalPrelude.Image

end OAI
