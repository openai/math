import OAI.Computability.BorderVNP.FiniteEvaluatorMergedRaw
import OAI.Computability.BorderVNP.FiniteDiagonalPublicTerms
import OAI.Computability.BorderVNP.FiniteEvaluatorTaskMatrices

/-! # Independent scalar-report matrices for the real owned host rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged

open Crossing Packing Packing.Inherited Packing.CellAddresses FiniteDiagonal
open BorderVNP.Cube Cube.Physical Cube.Scatter.Assignment FieldSiteDirectory
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 800000

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (bank : Ports bits) (z : V.Public R)
  (u : Fin (R+1)) (digits : ℕ) (rows : List Reports.Row)
  (order : Fin rows.length ≃ {c : L.Cell // V.cellOwner R z c = u})

/-- The exact fully staged sparse site and its delivered field word at an
owned row ordinal. -/
noncomputable abbrev rowSite (i : Fin rows.length) :=
  site N L.cell (order i).val V.siteID S.edgeID S.portID S.site

/-- Ordered delivered data at the physical source and destination ends,
followed by the genuine external arguments of this host cell. -/
noncomputable abbrev rowInput (i : Fin rows.length) :=
  Placement.endSupply N L.cell (order i).val S.edgeID S.portID bank
    (routedEnds L (V.owners R) (V.readPublic R z))

/-- The true integer signed-validator weight times the true field scalar
return from this particular native row. -/
noncomputable def rowScore (i : Fin rows.length) (claim : Fin (Fintype.card F) → Fin digits → Bool) : F :=
  ((validator (rowSite V R z u rows order i) digits (rowInput V R bank z u rows order i) claim).weight : F) *
    reportScalar digits claim

/-- Summing the genuine bit-major reports independently for all owned
rows produces the exact host factor of the checked global public term. -/
theorem owned_validators (loc : ∀ v, (S.site v).Local) (schema : ∀ v, (S.site v).Schema)
    (relative : ∀ v, (S.site v).RelativeBoxes)
    (codes : S.values = FieldPowers.entry (Fintype.equivFin F).symm)
    (locality : ∀ i, (rowSite V R z u rows order i).Local)
    (range : ∀ i, let s := rowSite V R z u rows order i
      ∀ (g : Fin s.work → Bool) obs, s.observe (Inherited.bits g (rowInput V R bank z u rows order i))=some obs →
        ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F)
    (fit : ∀ i, let s := rowSite V R z u rows order i
      ∀ (g : Fin s.work → Bool) obs, s.observe (Inherited.bits g (rowInput V R bank z u rows order i))=some obs →
        (obs.filterMap Prod.snd).length < 2^digits) :
    (∑ claims : TaskReadback.Matrices F digits rows, ∏ i,
      rowScore V R bank z u digits rows order i (claims i)) =
    ∏ c : {c : L.Cell // V.cellOwner R z c = u},
      ∑ g, S.rawCell L V.siteID (V.owners R) bank (V.readPublic R z) c.val g := by
  rw [← Fintype.prod_sum]
  refine (Finset.prod_congr rfl (fun i _ => validator_raw S L V.siteID (V.owners R) bank (V.readPublic R z) (order i).val
    digits loc schema relative codes (locality i) (range i) (fit i))).trans ?_
  exact order.prod_comp (fun c => ∑ g, S.rawCell L V.siteID (V.owners R) bank (V.readPublic R z) c.val g)

end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
