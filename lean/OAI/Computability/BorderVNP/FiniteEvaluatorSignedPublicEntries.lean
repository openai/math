import OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeInputs
import OAI.Computability.BorderVNP.FiniteEvaluatorPublicFiber

/-! # The scalar deck read by each team of a checked public word

On the true fragment-inclusive arena the local cube lookup returns one field
entry for each vertex that the reconstructed selectors assign to this team.
These are the same factors as the checked public word uses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube Cube.Physical Cube.Scatter Cube.Scatter.Assignment
open FiniteEvaluator CubeVisits RoutingISA VPVNP.BurstRAM
open scoped Classical BigOperators

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R) (u : Fin (R+1))
  (header profile cells cables maxRows stride : ℕ)
  (entry : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F) (params : SignedTaskArena.Parameters)
local notation "ar" => planArena L R header profile cells cables maxRows stride
local notation "sa" => signedPlanArena L R header profile cells cables maxRows stride entry params
local notation "base" => CubeHeaderInstall.Inputs.packetBase (CubeArena.Layout.header ar)
local notation "Y" => V.signedInputs R raw u header profile cells cables maxRows stride entry params

/-- The published scalar-return slots agree term by term with the cube table
of the recovered packet word, including for zero entries. -/
theorem signed_public_entries (fixed : ∀ p, L.table p=entry) :
    (∏ i, (Y).scalar i) = ∏ j : Fin (V.teamPairs R raw u).length,
      selected entry (FieldSiteDirectory.cubeInputs L (V.owners R) raw.1) ((V.teamPairs R raw u).get j) := by
  let frame := (sa).lookupFrame (V.teamPairs R raw u).length
  refine (V.cubeInputs_product R raw u base frame rfl entry (ar).stop (sa).after.ids fixed).trans ?_
  apply Finset.prod_congr rfl
  intro j _
  unfold teamEntry
  rw [fixed]
  rfl

/-- On a passing branch, the physically indexed cube scalar factor and
the owned host-cell factors are precisely the checked public team value. -/
theorem ownedPublicValue_signed (fixed : ∀ p, L.table p=entry) (bank : Ports bits)
    (z : V.Public R) (decoded : V.readPublic R z=raw.1) :
    V.ownedPublicValue R entry bank z u =
      (∏ c : {c : L.Cell // V.cellOwner R z c=u},
        ∑ g, S.rawCell L V.siteID (V.owners R) bank raw.1 c.val g) * ∏ i, (Y).scalar i := by
  let host (q : Physical.NativeAssignments.Routed (b:=L.bitWidth) (s:=L.supply) (V.owners R)) :=
    ∏ c : {c : L.Cell // V.cellOwner R z c=u}, ∑ g, S.rawCell L V.siteID (V.owners R) bank q c.val g
  let vertex (q : Physical.NativeAssignments.Routed (b:=L.bitWidth) (s:=L.supply) (V.owners R)) :=
    let visits := teamList (chosen L.bitWidth L.supply q.1) L.blocks (V.owners R q.1) u
    ∏ j : Fin visits.length, selected entry (FieldSiteDirectory.cubeInputs L (V.owners R) q) (visits.get j)
  refine (congrArg (fun q => host q*vertex q) decoded).trans ?_
  exact congrArg (host raw.1 * ·) (V.signed_public_entries R raw u header profile cells cables maxRows stride entry params fixed).symm

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
