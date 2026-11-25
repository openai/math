import OAI.Computability.BorderVNP.RoutingISASignedPrepInputCut
import OAI.Computability.BorderVNP.RoutingISASignedPrepArguments
import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedControlReturns

/-! # Admitted owned cube assignments and physical report rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Physical.NativeAssignments DiagonalTallyCellReports
open BorderVNP.FiniteEvaluator

variable {w : ℕ}

/-- Owned cell headers and their physical report and task allocations on the
particular state returned by the ownership scan. -/
structure LocalReportData (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) where
  /-- Addresses and word widths of the report traversal. -/
  layout : ReportLayout
  /-- Actual cells, in the returned ownership order. -/
  cells : List (ReportCell layout)
  /-- Initial report descriptor and counter cursors. -/
  cursor : ReportCursor
  /-- Width of a delivered private site record. -/
  description : ℕ
  seed : ∀ d : Returns controls pub mac s m, PreparedReportInput pub d.val.2.2 cells cursor description
  /-- Fitted argument writers on each particular report assignment. -/
  argumentsFit : ∀ (d : Returns controls pub mac s m) (rows : ReportAssignments cells),
    let r := assignedReportReturnEquiv (seed d) mac d.val.2.1 rows
    ArgumentInput pub mac r.val.2.1 r.val.2.2

private def restrictBase {A : Type*} {T : A → Type*} {P : A → Prop} (valid : ∀ a, T a → P a) :
    (Σ a, T a) ≃ Σ p : Subtype P, T p.val where
  toFun q := ⟨⟨q.1,valid q.1 q.2⟩,q.2⟩
  invFun p := ⟨p.1.val,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {R : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (decl : LengthDeclaration ar.n ar.header.d) (raw : Symbols ar.header.d → List Bool)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (pub : Fin (R+1) → Arg → Word w) (mac : Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : Fin (R+1) → Bank w) (mem : Fin (R+1) → Memory w)
    (constants : ∀ u, Returns (CubeConstants.install id) (pub u) (mac u) (reg u) (mem u))

local notation "Q" => Matching ar owners decl raw
set_option quotPrecheck false in
local notation "End" => OwnedRuns ar pub mac (fun u => (constants u).val.2.1) (fun u => (constants u).val.2.2)

/-- For the observed public declaration and raw shared rows, the true signed
builders are indexed by a compatible routed cube assignment satisfying all
physical zero pins, followed by an independent assignment of the report digits
at each team's actual received cells. The ownership equivalence is supplied
by `SharedWriters.physicalOwnedEquiv` and the control relation by
`SharedWriters.controls_iff_pins`. -/
noncomputable def nativeOwnedReportEquiv (owned : End ≃ Q) (pins : Q → Prop)
    (controlsAt : Q → Fin (R+1) → OpenSuffix.Inputs)
    (controlPaths : ∀ a : Q, let z := owned.symm a
      OpenSuffix.ControlFamily (controlsAt a) pub mac (fun u => (z u).val.2.1) (fun u => (z u).val.2.2) (pins a))
    (data : ∀ a : Subtype pins, ∀ u, let z := owned.symm a.val u
      LocalReportData (pub u) (mac u) z.val.2.1 z.val.2.2) :
    ((u : Fin (R+1)) → Returns (signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s))
      (pub u) (mac u) (reg u) (mem u)) ≃
      Σ a : Subtype pins, (u : Fin (R+1)) → ReportAssignments (data a u).cells := by
  let tail (q : Q) := (u : Fin (R+1)) → LocalTail (pub u) (mac u) (owned.symm q u).val.2.1 (owned.symm q u).val.2.2
  have pin (q : Q) (x : tail q) : pins q := (controlPaths q).returns.mp ⟨fun u => (x u).1⟩
  let positive (q : Subtype pins) := ((controlPaths q.val).returns.mpr q.property).some
  let rows (q : Subtype pins) (u : Fin (R+1)) :=
    fittedReportTailEquiv (pub := pub u) (mac := mac u) (positive q u) ((data q u).seed (positive q u))
      ((data q u).argumentsFit (positive q u))
  exact (jointInputCut id pub mac reg mem constants).trans ((Equiv.sigmaCongrLeft' owned).trans
    ((restrictBase (T := tail) pin).trans (Equiv.sigmaCongrRight fun q => Equiv.piCongrRight (rows q))))

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
