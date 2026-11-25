import OAI.Computability.BorderVNP.FiniteDiagonalOwnedCellProduct
import OAI.Computability.BorderVNP.CubeScatterTransmissionRoutedValue
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeVisitTeams

/-! # Contracting the independent private work in each received public term

Once the epoch, selector words and the delivered and co-located payloads
are fixed, the finite-field validator and scalar calls can sum each cell's
private work independently. The selected scalar table entries at cube
vertices are then read in the actual team visit order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube Cube.Physical Cube.Scatter.Assignment Physical.NativeAssignments
open FiniteEvaluator.CubeVisits
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 800000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S)

/-- The checked words at the interface between routed data preparation
and the independent owned-cell private computations. -/
abbrev Public (R : ℕ) :=
  {z : Routed.Words L.dimension L.alphabet (Fin (R+1)) // Routed.Accepts L.bitWidth L.supply (V.owners R) z}

/-- Recovered selected packets and physically routed bits for a public word. -/
noncomputable def readPublic (R : ℕ) (z : V.Public R) := (Routed.wordsEquiv (V.owners R) L.bitWidth L.supply).symm z

/-- The assigned public factor after summing all genuine private cell work. -/
noncomputable def publicValue (R : ℕ) (x : Ports bits) (z : V.Public R) : F :=
  let q := V.readPublic R z
  (if FieldSiteDirectory.pinsPass L (V.owners R) q then
    ∏ c, ∑ g, S.rawCell L V.siteID (V.owners R) x q c g else 0) *
      cubeTermWeight L.table (fun _ _ => 1) (FieldSiteDirectory.cubeInputs L (V.owners R) q)

/-- Full scalar contraction over only the public and delivered choices,
with all signed and field-valued local work summed in its own physical cell. -/
theorem value_eq_public (R : ℕ) (x : Ports bits) :
    let e := Routed.wordsEquiv (V.owners R) L.bitWidth L.supply
    letI := Fintype.ofEquiv _ e
    N.value T x = ∑ z : V.Public R, V.publicValue R x z := by
  intro e
  let : Fintype (V.Public R) := Fintype.ofEquiv _ e
  rw [S.value_eq_raw_sum L V.siteID (V.owners R) x,Fintype.sum_prod_type]
  refine Eq.trans ?_ (e.symm.sum_comp (fun q =>
    (if FieldSiteDirectory.pinsPass L (V.owners R) q then
      ∏ c, ∑ g, S.rawCell L V.siteID (V.owners R) x q c g else 0) *
        cubeTermWeight L.table (fun _ _ => 1) (FieldSiteDirectory.cubeInputs L (V.owners R) q))).symm
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro q _
  exact S.sum_flat_cells L V.siteID (V.owners R) x q

/-- The true owner of a host cell at the physically chosen coordinate. -/
noncomputable def cellOwner (R : ℕ) (z : V.Public R) (c : L.Cell) : Fin (R+1) :=
  let q := V.readPublic R z
  V.owners R q.1 (L.label c (chosen L.bitWidth L.supply q.1))

/-- Product of the contracted host cells and all cube scalar visits of one
team, in the actual owned-vertex enumeration. -/
noncomputable def ownedPublicValue (R : ℕ) (entry : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
    (x : Ports bits) (z : V.Public R) (u : Fin (R+1)) : F :=
  let q := V.readPublic R z
  let a := FieldSiteDirectory.cubeInputs L (V.owners R) q
  let visits := teamList (chosen L.bitWidth L.supply q.1) L.blocks (V.owners R q.1) u
  (∏ c : {c : L.Cell // V.cellOwner R z c = u}, ∑ g, S.rawCell L V.siteID (V.owners R) x q c.val g) *
    ∏ j : Fin visits.length, selected entry a visits[j]

/-- Every physical team contributes its host cells and cube vertices once
at the selected public word. Any failing unused-bit test contributes zero. -/
theorem public_eq_owned (R : ℕ) (entry : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
    (same : ∀ p, L.table p = entry) (x : Ports bits) (z : V.Public R) :
    V.publicValue R x z =
      if FieldSiteDirectory.pinsPass L (V.owners R) (V.readPublic R z) then
        ∏ u, V.ownedPublicValue R entry x z u else 0 := by
  let q := V.readPublic R z
  let a := FieldSiteDirectory.cubeInputs L (V.owners R) q
  unfold publicValue
  dsimp only
  split_ifs with hp
  · simp only [ownedPublicValue,Finset.prod_mul_distrib]
    apply congrArg₂ (· * ·)
    · exact (Fintype.prod_fiberwise (V.cellOwner R z) (fun c => ∑ g, S.rawCell L V.siteID (V.owners R) x q c g)).symm
    · have ht : L.table = fun _ => entry := funext same
      rw [ht]
      exact (cube_product (chosen L.bitWidth L.supply q.1) (V.owners R q.1) entry a).symm
  · exact zero_mul _

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
