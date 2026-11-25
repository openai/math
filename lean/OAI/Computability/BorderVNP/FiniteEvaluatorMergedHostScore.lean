import OAI.Computability.BorderVNP.FiniteEvaluatorMergedHostRows
import OAI.Computability.BorderVNP.PackedInheritedMergedOrdinal

/-! # The post-splice native host product at the routed physical cell inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged

open Crossing Packing Packing.Inherited FiniteDiagonal FiniteDiagonal.CellTrace BorderVNP.Cube BorderVNP.Cube.Physical
open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket.Supplement TeamRAM
open scoped Classical BigOperators

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (bank : Ports bits) (z : V.Public R)
  (u : Fin (R+1)) (digits : ℕ) (rows : List Reports.Row)
  (order : Fin rows.length ≃ {c : L.Cell // V.cellOwner R z c = u})
  {Orig : Type} {w : ℕ} (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (owned : ℕ → Batch.Owned Orig)
  (supplied : ℕ → List Bool) (claim : ℕ → Fin (Fintype.card F) → Fin digits → Bool)

private noncomputable abbrev X := Reports.inputs l raw owned supplied (fun _ => digits) claim
local notation "site₀" i => rowSite V R z u rows order i
local notation "input₀" i => rowInput V R bank z u rows order i

/-- The true placed typed input and the merged validator coincide, from the
original sparse geometry fields, the delivered boundary order and the
same scalar report stream that the checker and scalar macro share. -/
theorem placed_validator {i : Fin rows.length}
    (geometry : (owned i.val).placed.directory = Placement.packet N L.cell (order i).val
      V.siteID S.edgeID S.portID S.site (Reports.fields (site₀ i).size (Fintype.card F) digits))
    (work : (owned i.val).placed.privateWires=(site₀ i).work)
    (external : (owned i.val).placed.external=supplied i.val++FiniteScalarRounds.stream F (claim i.val))
    (delivered : supplied i.val=List.ofFn (input₀ i)) :
    TypedBatch.cellInput (owned i.val).placed = validator (site₀ i) digits (input₀ i) (claim i.val) := by
  rw [← report_directory N L.cell (order i).val V.siteID S.edgeID S.portID S.site] at geometry
  unfold TypedBatch.cellInput validator
  rw [geometry,work,external,delivered]
  rfl

/-- Each actual native owned-row contribution is the physical merged row
score on its true public endpoints and chronological field-report matrix. -/
theorem hostFactor_rowScore (pub : Arg → Word w) (m : Memory w) (published : readings m=l.published raw)
    (apart : Reports.MetaOutside l (l.before raw l.cells) owned) {n : ℕ}
    (ready : Cells.Prepared (X digits l raw owned supplied claim) pub
      (Batch.written m (fun j => (owned j).cell) (l.before raw l.cells)) n)
    (count : l.before raw l.cells=rows.length)
    (geometry : ∀ i : Fin rows.length, (owned i.val).placed.directory = Placement.packet N L.cell (order i).val
      V.siteID S.edgeID S.portID S.site (Reports.fields (site₀ i).size (Fintype.card F) digits))
    (work : ∀ i : Fin rows.length, (owned i.val).placed.privateWires=(site₀ i).work)
    (delivered : ∀ i : Fin rows.length, supplied i.val=List.ofFn (input₀ i)) :
    (X digits l raw owned supplied claim).hostFactor pub
      (Batch.written m (fun j => (owned j).cell) (l.before raw l.cells)) =
      ∏ i : Fin rows.length, rowScore V R bank z u digits rows order i (claim i.val) := by
  rw [Reports.hostFactor_after_splice _ _ _ _ _ _ _ _ published apart ready]
  have cast : (∏ i : Fin (l.before raw l.cells), ((TypedBatch.cellInput (owned i.val).placed).weight : F) *
      reportScalar digits (claim i.val)) = ∏ i : Fin rows.length, ((TypedBatch.cellInput (owned i.val).placed).weight : F) *
      reportScalar digits (claim i.val) :=
    (finCongr count).prod_comp (fun i => ((TypedBatch.cellInput (owned i.val).placed).weight : F) * reportScalar digits (claim i.val))
  rw [cast]
  apply Finset.prod_congr rfl
  intro i _
  have data := ready.bank i.val (i.isLt.trans_eq count.symm)
  have hv := placed_validator V R bank z u digits rows order owned supplied claim (geometry i) (work i) data (delivered i)
  rw [hv]
  rfl

end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
