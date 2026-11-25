import OAI.Computability.BorderVNP.DiagonalNativeCellProduct
import OAI.Computability.BorderVNP.DiagonalNativePackedProduct

/-! # Expansion of the actual per-team preparations and owned sparse cell sums -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator
open scoped BigOperators Classical

variable {teams w n : ℕ} {gen : Fragment IO}
    {Prefix : Fin teams → Type} [∀ u, Fintype (Prefix u)]
    (pub : Fin teams → Arg → Word w) (mem : ∀ u, Prefix u → Memory w)
    (rows : ∀ u a, GeneratedCells gen n (pub u) (mem u a))

/-- Physical cell IDs for one tuple of completed preparations. Each team
sees its actual directory and executes exactly the rows of its own group. -/
structure JoinedCells (a : ∀ u, Prefix u) where
  /-- The cell names of this profile's attained network. -/
  Cell : Type
  [finite : Fintype Cell]
  /-- Native row enumeration at each team. -/
  order : ∀ u, Fin (Frame.ofMemory (pub u) (mem u (a u))).count ≃ Cell
  /-- Chosen owner of each cell, after the true selector-length declaration. -/
  owner : Cell → Fin teams
  /-- Exact sparse private cell input at its owning team. -/
  cells : Cell → CellInput
  /-- The stored team number equals the running team. -/
  teamAt : ∀ u, (Frame.ofMemory (pub u) (mem u (a u))).team = u.val
  /-- The native ownership test sees the actual group owner's number. -/
  ownerAt : ∀ u (i : Fin (Frame.ofMemory (pub u) (mem u (a u))).count),
    (mem u (a u) ((Frame.ofMemory (pub u) (mem u (a u))).address i.val)).val = (owner (order u i)).val
  /-- The physically supplied generated input on each owned row is this cell's input. -/
  cellAt : ∀ u (i : Fin (Frame.ofMemory (pub u) (mem u (a u))).count),
    owner (order u i) = u → (rows u (a u)).cell i.val = cells (order u i)

attribute [instance] JoinedCells.finite

section

variable {pub mem rows}

/-- The actual guessed interior bit vectors in every cell of this prepared
profile, in the order consumed by its generated sparse statement. -/
abbrev JoinedCells.Private {a : ∀ u, Prefix u} (J : JoinedCells pub mem rows a) :=
  (c : J.Cell) → Fin (J.cells c).privateWires → Bool

/-- Signed output of the private cell programs on those precise guessed
bits followed by the true external argument wires. -/
noncomputable def JoinedCells.privateWeight {a : ∀ u, Prefix u} (J : JoinedCells pub mem rows a)
    (z : J.Private) : ℤ :=
  ∏ c, (J.cells c).directory.weight (CellSparse.lookup (List.ofFn (z c) ++ (J.cells c).external))

end

/-- All true preparation rows and their private cell inputs can be summed
globally before evaluating the tally continuation. Each cell contributes
once regardless of the number of teams and of its current public owner. -/
theorem joint_private_sum (state : ∀ u, Prefix u → ℤ) (reader : ∀ u, Prefix u → ℤ)
    (joint : ∀ a : ∀ u, Prefix u, JoinedCells pub mem rows a) :
    (∏ u : Fin teams, ∑ a : Prefix u, state u a * ((rows u a).product * reader u a)) =
    ∑ a : ∀ u, Prefix u, ∑ z : (joint a).Private,
      (∏ u, state u (a u)) * (joint a).privateWeight z * (∏ u, reader u (a u)) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _))
  intro a _
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  let J := joint a
  have cell := all_ownedRows_private_sum (fun u => Frame.ofMemory (pub u) (mem u (a u)))
    (fun u => mem u (a u)) J.order J.owner (fun u => (rows u (a u)).cell) J.cells J.teamAt J.ownerAt J.cellAt
  change _ * ((∏ u, (rows u (a u)).product) * _) = _
  change (∏ u, (rows u (a u)).product) = ∑ z : J.Private, J.privateWeight z at cell
  rw [cell,← mul_assoc,Finset.mul_sum,Finset.sum_mul]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
