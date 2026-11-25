import OAI.Computability.BorderVNP.FiniteEvaluatorMergedValue

/-! # Field reports restore the original host tensor at its two routed endpoints -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged

open Crossing Packing Packing.CellAddresses Packing.Inherited CellSparse
open FiniteDiagonal FiniteDiagonal.FieldSiteDirectory BorderVNP.Cube Cube.Physical Cube.Physical.NativeAssignments Cube.Scatter.Assignment
open private privateWires_append privateStaging_append from OAI.Computability.BorderVNP.CubePhysicalNativeAssignments
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 800000

variable {D ns teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] {T : N.Tables F} (S : FieldSiteDirectory N T) (L : FieldPacketPlan N F)
  (siteID : N.Site ↪ Fin ns)
  (owners : (Packet L.dimension L.alphabet L.blocks → Selector L.dimension L.alternatives L.copies) →
    Fin L.alphabet → Fin teams)
  (bank : Ports bits) (q : Routed (b := L.bitWidth) (s := L.supply) owners) (c : L.Cell)

private noncomputable abbrev incomingBits := Placement.endSupply N L.cell c S.edgeID S.portID bank (routedEnds L owners q)

/-- Original work assignments at each site vary independently after fixing
the genuine internal wires. They realize exactly the cell's true field table. -/
theorem raw_factors :
    (∑ g : Fin (externalBase N L.cell c S.workWidth) → Bool,
      S.rawCell L siteID owners bank q c g) =
    ∑ g, CellAddresses.factor N L.cell c S.edgeID S.portID T g (incomingBits S L owners bank q c) := by
  let score := S.rawCell L siteID owners bank q c
  let incoming := incomingBits S L owners bank q c
  refine ((Fin.appendEquiv (α := Bool) (guessedSize N L.cell c) (siteSize N L.cell c S.workWidth)).sum_comp score).symm.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  let value := fun (v : {v : N.Site // L.cell v = c}) (z : Fin (S.site v.val).work → Bool) =>
    ((S.site v.val).observe (Inherited.bits z
      (Placement.canonical N L.cell c S.edgeID S.portID v g incoming ∘ Fin.cast (S.incoming v.val)))).elim 0
        (fieldWeight S.values)
  let total := fun (z : ∀ v : {v : N.Site // L.cell v = c}, Fin (S.site v.val).work → Bool) =>
    ∏ v, value v (z v)
  calc
    _ = ∑ a, total (siteWords N L.cell c siteID S.workWidth a) := by
      apply Finset.sum_congr rfl
      intro a _
      change S.rawCell L siteID owners bank q c (Fin.append g a) = _
      simp only [rawCell,privateWires_append,privateStaging_append]
      rfl
    _ = ∑ z, total z := (siteWords N L.cell c siteID S.workWidth).sum_comp total
    _ = ∏ v, ∑ z, value v z := (Fintype.prod_sum value).symm
    _ = _ := by
      unfold CellAddresses.factor
      apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
      intro v _
      exact S.models v.val (fun e j => (wire N L.cell c S.edgeID S.portID v e j).elim g incoming)
        (fun p j => incoming (port N L.cell c S.edgeID S.portID v p j))

/-- Eliminating the forced incidence slots of the true merged packet yields
precisely the original private-work sum at the actual independent cable ends. -/
theorem value_raw (loc : ∀ v, (S.site v).Local) (schema : ∀ v, (S.site v).Schema)
    (relative : ∀ v, (S.site v).RelativeBoxes) :
    (site N L.cell c siteID S.edgeID S.portID S.site).value (fieldWeight S.values) (incomingBits S L owners bank q c) =
      ∑ g : Fin (externalBase N L.cell c S.workWidth) → Bool, S.rawCell L siteID owners bank q c g :=
  (value_factors N L.cell c siteID S.edgeID S.portID S.site S.incoming loc schema relative S.values T S.models _).trans
    (raw_factors S L siteID owners bank q c).symm

section
variable [Fintype F] (digits : ℕ)

/-- Summing exactly the native signed compact-validator output times its
actual bit-major field return over reports recovers the owned-cell
summand on this history, including true zero scalar entries. -/
theorem validator_raw (loc : ∀ v, (S.site v).Local) (schema : ∀ v, (S.site v).Schema)
    (relative : ∀ v, (S.site v).RelativeBoxes)
    (codes : S.values = FieldPowers.entry (Fintype.equivFin F).symm)
    (locality : (site N L.cell c siteID S.edgeID S.portID S.site).Local)
    (range : let s := site N L.cell c siteID S.edgeID S.portID S.site
      ∀ (g : Fin s.work → Bool) obs, s.observe (Inherited.bits g (incomingBits S L owners bank q c))=some obs →
        ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F)
    (fit : let s := site N L.cell c siteID S.edgeID S.portID S.site
      ∀ (g : Fin s.work → Bool) obs, s.observe (Inherited.bits g (incomingBits S L owners bank q c))=some obs →
        (obs.filterMap Prod.snd).length < 2^digits) :
    let s := site N L.cell c siteID S.edgeID S.portID S.site
    (∑ report : Fin (Fintype.card F) → Fin digits → Bool,
      ((validator s digits (incomingBits S L owners bank q c) report).weight : F) * reportScalar digits report) =
    ∑ g : Fin (externalBase N L.cell c S.workWidth) → Bool, S.rawCell L siteID owners bank q c g := by
  intro s
  rw [sum_validator s digits locality _ range fit,←codes]
  exact value_raw S L siteID owners bank q c loc schema relative

end
end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
