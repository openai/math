import OAI.Computability.BorderVNP.DiagonalJointAcceptedTerms
import OAI.Computability.BorderVNP.CellGuardedObservations

/-! # The private bits and checked observations of the physically owned cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.JoinedCells

open VPVNP.BurstRAM TeamContraction CellDispatch CellMacro.Generator CellSparse
open scoped BigOperators Classical

variable {teams w n : ℕ} {gen : Fragment IO} {Prefix : Fin teams → Type}
    {pub : Fin teams → Arg → Word w} {mem : ∀ u, Prefix u → Memory w}
    {rows : ∀ u a, GeneratedCells gen n (pub u) (mem u a)} {pre : ∀ u, Prefix u}
    (J : JoinedCells pub mem rows pre)

/-- Identify the private bits of every issued native call with the actual
flat bank at the corresponding cell. The width includes both its internal
cables and the staged site words. -/
def bankEquiv {Cell : Type} (number : J.Cell ≃ Cell) (size : Cell → ℕ)
    (width : ∀ c, (J.cells c).privateWires = size (number c)) :
    J.Private ≃ ((c : Cell) → Fin (size c) → Bool) :=
  Equiv.piCongr number fun c => Equiv.arrowCongr (finCongr (width c)) (Equiv.refl Bool)

/-- Reading a transported bank digit gives the corresponding literal
private choice at its true cell and offset. -/
theorem bankEquiv_read {Cell : Type} (number : J.Cell ≃ Cell) (size : Cell → ℕ)
    (width : ∀ c, (J.cells c).privateWires = size (number c))
    (z : J.Private) (c : J.Cell) (i : Fin (J.cells c).privateWires) :
    J.bankEquiv number size width z (number c) (Fin.cast (width c) i) = z c i := by
  rw [bankEquiv,Equiv.piCongr_apply_apply]
  rfl

/-- The addressed physical word sequence presented to one signed sparse
checker, including the guessed private bank followed by the delivered
external data and its reported subtotals. -/
def bankAt (z : J.Private) (c : J.Cell) : ℕ → Bool :=
  lookup (List.ofFn (z c) ++ (J.cells c).external)

/-- Joint passing is exactly one successful guarded observation list
and truthful report for each actual cell. -/
theorem privateWeight_ne_zero_iff (free : ∀ c, (J.cells c).directory.SignFree) (z : J.Private) :
    J.privateWeight z ≠ 0 ↔ ∀ c, ∃ os, (J.cells c).directory.guardedObservations (J.bankAt z c) = some os ∧
      countsValid (J.bankAt z c) (J.cells c).directory.reportedCounts os := by
  unfold privateWeight
  rw [Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ,forall_const]
  apply forall_congr' fun c => ?_
  rw [(free c).weight_guarded]
  change (if _ then (1:ℤ) else 0) ≠ 0 ↔ _
  split_ifs with h <;> simp_all [bankAt]

/-- Every passing physical assignment has unit sign, regardless of the
field scalar identified by any one of its selected table positions. -/
theorem privateWeight_one (free : ∀ c, (J.cells c).directory.SignFree) (z : J.Private)
    (passed : J.privateWeight z ≠ 0) : J.privateWeight z = 1 := by
  have all := (J.privateWeight_ne_zero_iff free z).mp passed
  apply Finset.prod_eq_one
  intro c _
  exact ((free c).weight_guarded _).trans (ite_eq_left (all c))

end RoutingISA.Evaluator.JoinedCells

end BorderVNP
end Computability
end OAI
