import OAI.Computability.BorderVNP.DiagonalNativePositivePacket
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling
import OAI.Computability.BorderVNP.DiagonalNativeTypedRows

/-! # Actual task inputs at the final instruction of a signed preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally

variable {dim box lanes selectors symbols w : ℕ}
variable (id : TableEntry dim box lanes selectors symbols → ℕ)
variable (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) {s : Bank w} {m : Memory w}

/-- Final public report return, immediately before writing the typed task directory. -/
abbrev reportReturn (v : Visits id pub mac s m) := v.reports

/-- The true task producers and final seven-word serializer on the saved report state. -/
abbrev TypedParts (v : Visits id pub mac s m) :=
  Σ a : Returns beforeTyped pub mac (reportReturn id pub mac v).val.2.1 (reportReturn id pub mac v).val.2.2,
    Returns TypedBatch.entry pub mac a.val.2.1 a.val.2.2

private noncomputable def argumentEquiv (v : Visits id pub mac s m) :
    TypedParts id pub mac v ≃ Returns arguments pub mac (reportReturn id pub mac v).val.2.1 (reportReturn id pub mac v).val.2.2 :=
  (seqReturnEquiv beforeTyped TypedBatch.entry pub mac (reportReturn id pub mac v).val.2.1
    (reportReturn id pub mac v).val.2.2).trans (Equiv.subtypeEquivRight fun _ => (arguments_split pub mac).symm)

/-- The true boundaries of one signed preparation's typed task and input construction. -/
noncomputable def typedParts (v : Visits id pub mac s m) : TypedParts id pub mac v :=
  (argumentEquiv id pub mac v).symm v.arguments

/-- Final typed publication and the original complete native preparation have exactly
the same outgoing register bank and memory. -/
theorem typedParts_state (v : Visits id pub mac s m) :
    (typedParts id pub mac v).2.val.2 = (visitsEquiv id pub mac s m v).val.2 :=
  (congrArg (fun z => z.val.2) ((argumentEquiv id pub mac v).apply_symm_apply v.arguments)).trans
    (visitsEquiv_outState id pub mac v).symm

end RoutingISA.Evaluator.SignedPrep

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CompactMachine CellDispatch CellMacro.Generator BorderVNP.Cube
open TeamContraction.ProcessorSlots
variable {dim box lanes selectors symbols w k : ℕ}
variable (id : TableEntry dim box lanes selectors symbols → ℕ)
variable (pub : Arg → Word w) (routines : TeamOpcode.Macros w 8) (gen : Fragment IO) (n : ℕ)
variable (s : Bank w) (m : Memory w)
variable (pins : (Fin k → Bool) ≃ Pins.Return pub (install gen n routines) s m)
local notation "mac" => install gen n routines

/-- The actual typed source data before the last native writer determine the local
cell and payload function and certify the final dispatch directory for each true prefix. -/
theorem signedPrep_generated (b : Fin k → Bool) (p : SignedPreps id pub routines gen n s m pins b) :
    let v := (SignedPrep.visitsEquiv id pub mac (pins b).val.2.1 (pins b).val.2.2).symm p
    let cut := SignedPrep.typedParts id pub mac v
    ∀ rows : TypedRowsAt gen n pub cut.1.val.2.2,
      ∃ C : GeneratedCells gen n pub p.val.2.2, C.cell = rows.cells ∧ C.payload = rows.payload ∧
        let f := Frame.ofMemory pub p.val.2.2
        f.base+3*f.count ≤ 2^w := by
  intro v cut rows
  have final := SignedPrep.typedParts_state id pub mac v
  rw [show SignedPrep.visitsEquiv id pub mac (pins b).val.2.1 (pins b).val.2.2 v=p from Equiv.apply_symm_apply _ _] at final
  change cut.2.val.2 = p.val.2 at final
  rw [← final]
  exact rows.returned cut.2

/-- A window together with the real typed sources produces the positive team's entire
local continuation. Each prefix retains the exact logical input and physical payload
functions of the row model selected for that prefix. -/
theorem exists_positive_continuation {used limit : ℕ}
    (window : SignedStageWindow id pub routines gen n s m pins used limit)
    (rows : ∀ b (p : SignedPreps id pub routines gen n s m pins b),
      let v := (SignedPrep.visitsEquiv id pub mac (pins b).val.2.1 (pins b).val.2.2).symm p
      TypedRowsAt gen n pub (SignedPrep.typedParts id pub mac v).1.val.2.2) :
    ∃ C : PositiveContinuation id gen n pub routines s m pins used limit, ∀ b p,
      (C.cells b p).cell = (rows b p).cells ∧ (C.cells b p).payload = (rows b p).payload := by
  classical
  have existsRows b p := signedPrep_generated id pub routines gen n s m pins b p (rows b p)
  let C : PositiveContinuation id gen n pub routines s m pins used limit :=
    ⟨fun b p => (existsRows b p).choose,fun b p => (existsRows b p).choose_spec.2.2,window⟩
  exact ⟨C,fun b p => ⟨(existsRows b p).choose_spec.1,(existsRows b p).choose_spec.2.1⟩⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
