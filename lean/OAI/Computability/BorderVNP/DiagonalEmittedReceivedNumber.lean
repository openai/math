import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The original global number of every received compact ordinal -/

namespace Cube.Physical.NativeAssignments

open DiagonalTallyCellReports

/-- Reindexing an emitted array by its true length recovers the received row number at the
same natural ordinal. -/
theorem ReceivedRows.emittedNumber {T C n : ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (u : Fin T) (size : n=(R.cells u).length) (number : Fin n → Fin C) (global : ℕ → ℕ)
    (read : ∀ j, (number j).val=global j.val)
    (scheduled : ∀ j, number j=R.order ⟨u,Fin.cast size j⟩) :
    ∀ i : Fin (R.cells u).length, (R.cells u)[i].number=global i.val := by
  intro i
  let j := Fin.cast size.symm i
  have ij : Fin.cast size j=i := Fin.ext rfl
  have row := scheduled j
  rw [ij] at row
  exact (R.number u i).trans ((congrArg Fin.val row).symm.trans (read j))

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
