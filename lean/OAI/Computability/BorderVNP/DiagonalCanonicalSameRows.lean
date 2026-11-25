import OAI.Computability.BorderVNP.DiagonalGuardedReportTransport

/-! # Reindexing the canonical reports of the addressed unchecked candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator
open DiagonalTallyCellReports

variable {T w n : ℕ} {l l' : Fin T → ReportLayout}
    {xs : ∀ u,List (AssignedCell (l u))} {ys : ∀ u,List (AssignedCell (l' u))}

/-- The actual roster equality identifies the unchecked candidate's finite
report vector with the physical vector of the received directory. -/
def reportsOfSameRows (layout : l=l') (cells : HEq xs ys) : NativeReports xs ≃ NativeReports ys := by
  subst l'
  obtain rfl := eq_of_heq cells
  exact Equiv.refl _

/-- In the original directory the dependent report transport acts as the
identity for any witnesses of its row and chart equalities. -/
theorem reportsOfSameRows_self (layout : l=l) (cells : HEq xs xs) (r : NativeReports xs) :
    reportsOfSameRows layout cells r=r := rfl

/-- Transporting the canonical report on a fixed roster gives the same
canonical report obtained from the corresponding per-cell passing guards. -/
theorem canonicalReports_sameRows (layout : l=l') (cells : HEq xs ys)
    (pass : ∀ u c,c ∈ xs u → c.Passing w n) :
    reportsOfSameRows layout cells (canonicalReports xs pass)=canonicalReports ys
      (passing_of_same_rows layout.symm cells.symm pass) := by
  subst l'
  obtain rfl := eq_of_heq cells
  rfl

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
