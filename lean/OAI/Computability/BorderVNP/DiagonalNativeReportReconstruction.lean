import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedReports
import OAI.Computability.BorderVNP.RoutingISASignedPrepRows

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The physical per-team suffix returned by the joint native report bijection -/

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Physical.NativeAssignments DiagonalTallyCellReports
open BorderVNP.FiniteEvaluator

variable {w : ℕ}

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

/-- On any simultaneous proposal, the suffix for each team consists of its
selected four control calls, sampled chronological report, and actual fitted
argument return after those same report words. -/
theorem nativeOwnedReportEquiv_rebuilt (owned : End ≃ Q) (pins : Q → Prop)
    (controlsAt : Q → Fin (R+1) → OpenSuffix.Inputs)
    (controlPaths : ∀ a : Q, let z := owned.symm a
      OpenSuffix.ControlFamily (controlsAt a) pub mac (fun u => (z u).val.2.1) (fun u => (z u).val.2.2) (pins a))
    (data : ∀ a : Subtype pins, ∀ u, let z := owned.symm a.val u
      LocalReportData (pub u) (mac u) z.val.2.1 z.val.2.2)
    (a : Subtype pins) (rows : (u : Fin (R+1)) → ReportAssignments (data a u).cells) (u : Fin (R+1)) :
    let physical := owned.symm a.val u
    let ctl := ((controlPaths a.val).returns.mpr a.property).some u
    let d := data a u
    let tail := (fittedReportTailEquiv ctl (d.seed ctl) (d.argumentsFit ctl)).symm (rows u)
    let input := (nativeOwnedReportEquiv ar owners decl raw id pub mac reg mem constants owned pins
      controlsAt controlPaths data).symm ⟨a,rows⟩
    input u=(inputCut id (pub u) (mac u) (constants u)).symm ⟨physical,tail⟩ := by
  rfl

/-- Unsorting the declared report rows restores the unique compatible
physical word table and leaves every proposed report on its original team. -/
theorem jointRowReportsEquiv_rebuilt
    (pins : ∀ raw : SharedWords ar decl, Matching ar owners decl raw.val → Prop)
    (layout : ∀ (raw : SharedWords ar decl), Subtype (pins raw) → Fin (R+1) → ReportLayout)
    (cells : ∀ (raw : SharedWords ar decl) (a : Subtype (pins raw)) (u : Fin (R+1)), List (ReportCell (layout raw a u)))
    (pn : PinnedDeclared ar owners decl pins)
    (rows : let x := (pinnedMatchingEquiv ar owners decl pins).symm pn
      (u : Fin (R+1)) → ReportAssignments (cells x.1 x.2 u)) :
    let x := (pinnedMatchingEquiv ar owners decl pins).symm pn
    (jointRowReportsEquiv ar owners decl pins layout cells).symm ⟨pn,rows⟩=⟨x.1,x.2,rows⟩ := by
  rfl

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
