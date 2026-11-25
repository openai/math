import OAI.Computability.BorderVNP.DiagonalPositiveOwnedReportInputs
import OAI.Computability.BorderVNP.DiagonalPositiveReportMap

/-! # Choosing all issued cell bank widths before any private core is guessed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs
open RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine RoutingISA.CellDispatch DiagonalTallyCellReports
open scoped Classical

variable {D C ns ne np n d blocks b h K s T : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle) (q : Routed (b:=b) (s:=s) owners)
    (old new : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

local notation3 (prettyPrint := false) "ss(" a ")" => R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q a

/-- The proposal stays at the same actual owner and row when the private
core bits change. The received directory fixes its shape before dispatch. -/
def reportsAtCore (rr : NativeReports (ss(old))) : NativeReports (ss(new)) := fun u =>
  ⟨(rr u).val,(rr u).property.trans (congrArg eraseReportBits
    ((R.assigned_report N cell siteID edgeID portID state owners slot ports owner bottom q old u).trans
      (R.assigned_report N cell siteID edgeID portID state owners slot ports owner bottom q new u).symm))⟩

/-- Reindex the actual report returns by the original private inputs before
or after restoring the native report order. Both operations leave the
report byte stream of every issuing team exactly as received. -/
theorem reportsAtCore_physical (physical : ∀ u,List (ReportCell (layout u)))
    (same : ∀ u, eraseReportBits (physical u)=eraseReportBits (R.cells u))
    (r : (u : Fin T) → ReportAssignments (physical u)) :
    R.reportsAtCore N cell siteID edgeID portID state owners slot ports owner bottom q old new
      (R.physicalReportEquiv N cell siteID edgeID portID state owners slot ports owner bottom q old physical same r) =
      R.physicalReportEquiv N cell siteID edgeID portID state owners slot ports owner bottom q new physical same r := by
  funext u
  exact Subtype.ext rfl

variable (rr : NativeReports (R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q old))
    {dim box lanes selectors symbols w order : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    (S : Fin T → PositiveTeam id SparseExterior.driver order w) (p : ∀ u,(S u).Prefix)
    (team : Fin C → Fin T) (base : Fin T → ℕ)
    (table : ∀ u,OwnerTable (S u).pub ((S u).postMemory (p u)) ⟨u.val,base u,C⟩ (PositiveTeam.ownerWord team))
    (owned : ∀ u (i : Fin (R.cells u).length), team (R.order ⟨u,i⟩)=u)
    (X : NativeCallInputs R N cell siteID edgeID portID state owners slot ports owner bottom q old rr S p)

local notation3 (prettyPrint := false) "rr₁" =>
  R.reportsAtCore N cell siteID edgeID portID state owners slot ports owner bottom q old new rr

/-- The same receiving RAM and typed calls work at every choice of the core.
Only the separately issued private input vector will supply those digits. -/
def NativeCallInputs.atCore :
    NativeCallInputs R N cell siteID edgeID portID state owners slot ports owner bottom q new rr₁ S p where
  typed := X.typed
  published := X.published
  restored u i := X.restored u i

local notation3 (prettyPrint := false) "banks₀" =>
  R.privateBankEquiv N cell siteID edgeID portID state owners slot ports owner bottom q old rr S p team base table owned X

/-- The private-bank permutation and every finite coordinate cast can be
fixed at one preliminary vector, then used on the actual guessed vector,
with all report digits and the native state read from that same prefix. -/
noncomputable def reportImageAtCore :
    (PositiveTeam.joinOwnedRows S p team base table).ReportImage ((banks₀).symm new) (ss(new)) rr₁ :=
  R.reportImageOfNativeInputs N cell siteID edgeID portID state owners slot ports owner bottom q new rr₁ S p team base table
    owned (NativeCallInputs.atCore R N cell siteID edgeID portID state owners slot ports owner bottom q old new rr S p X)


include owned in
/-- Build the observed report image at an arbitrary candidate from the true
native calls at the all-zero private vector. The report proposal on both
sides is the physical pre-call proposal, and the public width proof can be
chosen before this private vector. -/
noncomputable def physicalReportImage (physical : ∀ u,List (ReportCell (layout u)))
    (same : ∀ u,eraseReportBits (physical u)=eraseReportBits (R.cells u))
    (r : (u : Fin T) → ReportAssignments (physical u))
    (hw : ∀ c : Fin C,(((S (team c)).generated (p (team c))).cell c.val).privateWires=externalBase N cell c (placedSize N state))
    (receipts : NativeCallInputs R N cell siteID edgeID portID state owners slot ports owner bottom q (fun _ _ => false)
      (R.physicalReportEquiv N cell siteID edgeID portID state owners slot ports owner bottom q (fun _ _ => false) physical same r) S p) :
    let dispatch := PositiveTeam.joinOwnedRows S p team base table
    dispatch.ReportImage ((dispatch.bankEquiv (Equiv.refl _)
      (fun c => externalBase N cell c (placedSize N state)) hw).symm new) (ss(new))
      (R.physicalReportEquiv N cell siteID edgeID portID state owners slot ports owner bottom q new physical same r) := by
  intro dispatch
  have observed := R.reportImageAtCore N cell siteID edgeID portID state owners slot ports owner bottom q (fun _ _ => false) new
    (R.physicalReportEquiv N cell siteID edgeID portID state owners slot ports owner bottom q (fun _ _ => false) physical same r)
    S p team base table owned receipts
  rw [reportsAtCore_physical] at observed
  exact observed

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
