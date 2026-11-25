import OAI.Computability.BorderVNP.FiniteDiagonalCubeHost
import OAI.Computability.BorderVNP.FiniteDiagonalCubeTerms

/-! # Scalar weight of a genuine assigned field packet plan

At each original site the table is read with the true private wire word and
the oriented public endpoint. Unused slots pin both independent ends to zero.
The remaining factors are the assigned scalar entries of the selected cubes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldPacketPlan

open Crossing Cube Cube.Physical Diagonal.CellEntries MvPolynomial
open scoped BigOperators Classical
open private scalarEval from OAI.Computability.BorderVNP.FiniteDiagonalCubeHost

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [CommRing F] (L : FieldPacketPlan N F)

/-- The scalar host table on the private wires and two independently opened
ends of each packet, with its actual slot padding tests. -/
noncomputable def scalarHost (T : N.Tables F) (x : Ports bits) (inside : ∀ c, N.InsideAssignment L.cell c)
    (single : SingleSlot L.dimension L.alphabet L.blocks (L.copies*L.bitWidth) → Bool)
    (ends : Packet L.dimension L.alphabet L.blocks → Ends L.dimension → Fin (L.copies*L.bitWidth) → Bool) : F :=
  if ∀ z ∉ Set.range L.slot, readEnd single ends false z = false ∧ readEnd single ends true z = false then
    ∏ c, ∏ v : {v : N.Site // L.cell v = c}, T v.val
      (fun i => siteWord N L.cell v.val i inside (fun dir j => readEnd single ends dir (L.slot j)))
      (fun p => x p.val)
  else 0

/-- The per-path weight computed by the actual plan factors into its scalar
host and exactly the individual entries of the selected cube tables. -/
theorem weight_eq_cubeTermWeight (T : N.Tables F) (x : Ports bits) (a : L.Path) :
    L.weight T x a = cubeTermWeight L.table (L.scalarHost T x a.1) a.2 := by
  simp only [weight, pathTag, globalEntry, scalarEval, cubeTermWeight, map_mul, map_prod,
    assignmentEntry, Network.read, packetTables, interpret_gadget, id_eq, eval_C]
  congr 1
  unfold host scalarHost
  split <;> simp only [cellTag, scalarTags, map_prod, interpret_gadget, id_eq, eval_C, map_zero]

end FiniteDiagonal.FieldPacketPlan

end BorderVNP
end Computability
end OAI
