import OAI.Computability.BorderVNP.DiagonalPositiveOwnedReports
import OAI.Computability.BorderVNP.DiagonalPositiveFinishReports

/-! # The simultaneous report and subtotal fiber on all unscreened native assignments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

variable {T w n : ℕ} {layout : Fin T → ReportLayout}

/-- Every count digit and use flag on the original frozen per-team rows,
with arbitrary proposed values. -/
abbrev NativeReports (ss : ∀ u, List (AssignedCell (layout u))) :=
  (u : Fin T) → ReportAssignments ((ss u).map AssignedCell.report)

/-- The one report family realized by the true fixed core's native returns. -/
noncomputable def canonicalReports (ss : ∀ u, List (AssignedCell (layout u)))
    (ok : ∀ u s, s ∈ ss u → s.Passing w n) : NativeReports ss :=
  fun u => (reportChoice_unique (ss u) (ok u)).choose.val.1

/-- This is an iff on arbitrary physical report data. It includes all cells,
including teams without any owned rows. -/
theorem nativeReports_iff (ss : ∀ u, List (AssignedCell (layout u)))
    (ok : ∀ u s, s ∈ ss u → s.Passing w n) (r : NativeReports ss) :
    (∀ u, ∃ ts, BatchReturns w n (ss u) (r u).val ts) ↔ r=canonicalReports ss ok := by
  constructor
  · intro returned
    funext u
    obtain ⟨ts,ret⟩ := returned u
    let z : ReportChoice w n (ss u) := ⟨(r u,ts),ret⟩
    exact congrArg (fun x : ReportChoice w n (ss u) => x.val.1)
      ((reportChoice_unique (ss u) (ok u)).choose_spec.2.2 z)
  · rintro rfl u
    let z := (reportChoice_unique (ss u) (ok u)).choose
    exact ⟨z.val.2,z.property⟩

end DiagonalTallyCellReports

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction TeamContraction.JointHeader CompactMachine CellMacro.Generator _root_.OAI.Computability.BorderVNP.Cube
open DiagonalTallyCellReports
open scoped BigOperators Classical

variable {axes box lanes selectors symbols T n w reserve groups cap dim width : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {p : PositiveFields reserve axes groups cap T dim width}

/-- Fixed public routing and one original private core, with all its physically
possible report and shared-claim bits. Native arithmetic receipts are required
only after the actual private checker accepts the reports. -/
structure NativeReportCandidate (id : TableEntry axes box lanes selectors symbols → ℕ)
    (gen : Fragment IO) (n w : ℕ) (p : PositiveFields reserve axes groups cap T dim width) where
  /-- The fixed native report layout at each team. -/
  layout : Fin T → ReportLayout
  /-- Original checked cells in native row order. -/
  assigned : ∀ u, List (AssignedCell (layout u))
  core : ∀ u s, s ∈ assigned u → s.Passing w n
  /-- Natural subtotals counted by the present physical owners. -/
  rows : Fin T → Fin dim → ℕ
  /-- The genuine positive machine at the proposed report and claim. -/
  team : NativeReports assigned → (Fin (T*dim*width) → Bool) → Fin T → PositiveTeam id gen n w
  /-- The actual global cell enumeration at those native prefixes. -/
  joined : ∀ r raw (a : (u : Fin T) → (team r raw u).Prefix),
    JoinedCells (fun u => (team r raw u).pub) (fun u => (team r raw u).postMemory) (fun u => (team r raw u).generated) a
  /-- Each team’s native preparation and the physical private choices. -/
  candidate : ∀ r raw, PositiveAssignment (team r raw) (joined r raw)
  /-- The genuine input bits at all the addressed private cells. -/
  image : ∀ r raw, (joined r raw (candidate r raw).1).ReportImage (candidate r raw).2 assigned r
  /-- Native selected operands at the accepted report bytes and arbitrary claim. -/
  input : ∀ raw u, let r := canonicalReports assigned core
    let S := team r raw u
    let a := (candidate r raw).1 u
    let mac := install gen n S.routines
    PositiveFields.FinishInput u rows width S.pub mac (cellBank S.pub mac a.2.val.2.1 a.2.val.2.2) a.2.val.2.2
      (p.withSubtotals raw).tallyWords
  widthFit : width ≤ w
  rowFit : ∀ u c, rows u c < 2^width
  sumFit : ∀ c, ∑ u,rows u c < 2^w

namespace NativeReportCandidate

variable (X : NativeReportCandidate id gen n w p)

/-- Specialize the native claim check to the actual passing report producer.
The private and public state are those from the same physical prefix. -/
noncomputable def atReports : PositiveClaimCandidate id gen n w p where
  rows := X.rows
  team := X.team (canonicalReports X.assigned X.core)
  joined := X.joined (canonicalReports X.assigned X.core)
  candidate := X.candidate (canonicalReports X.assigned X.core)
  input := X.input
  widthFit := X.widthFit
  rowFit := X.rowFit
  sumFit := X.sumFit

/-- The exact predicate used in the positive sum, on all raw report and
subtotal proposals, accepts precisely the two prescribed physical fields. -/
theorem pass_iff (r : NativeReports X.assigned) (raw : Fin (T*dim*width) → Bool) :
    positivePass (X.team r raw) (X.joined r raw) (X.candidate r raw) ↔
      r=canonicalReports X.assigned X.core ∧ raw=PositiveFields.canonicalSubtotals width X.rows := by
  have cells := ((X.joined r raw (X.candidate r raw).1).privateWeight_reports
    (X.candidate r raw).2 X.assigned r (X.image r raw) X.core).trans (nativeReports_iff X.assigned X.core r)
  constructor
  · rintro ⟨privateOK,tallies⟩
    have same := cells.mp privateOK
    subst r
    exact ⟨rfl,(X.atReports.tallyReturns_iff raw).mp tallies⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨cells.mpr rfl,(X.atReports.tallyReturns_iff _).mpr rfl⟩

/-- The true unscreened dependent sigma, filtered only by the original
native positive predicate, has exactly one element per routed passing
original private candidate. The inverse emits the actual native reports and
the physical owner rows' subtotal bits. -/
noncomputable def sourceEquiv {Source : Type*} (A : Source → NativeReportCandidate id gen n w p) :
    (Σ a : Source, Σ r : NativeReports (A a).assigned, {raw : Fin (T*dim*width) → Bool //
      positivePass ((A a).team r raw) ((A a).joined r raw) ((A a).candidate r raw)}) ≃ Source where
  toFun := Sigma.fst
  invFun a := ⟨a,canonicalReports (A a).assigned (A a).core,PositiveFields.canonicalSubtotals width (A a).rows,
    ((A a).pass_iff _ _).mpr ⟨rfl,rfl⟩⟩
  left_inv := by
    rintro ⟨a,r,raw,accepted⟩
    obtain ⟨rfl,rfl⟩ := ((A a).pass_iff r raw).mp accepted
    rfl
  right_inv _ := rfl

end NativeReportCandidate
end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
