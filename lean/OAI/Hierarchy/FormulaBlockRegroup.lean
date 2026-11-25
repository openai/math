import OAI.Hierarchy.FormulaPartitionCount
import OAI.Hierarchy.FormulaBlockFactors
import OAI.Hierarchy.GraphWireClass
import OAI.Hierarchy.GraphWireCoefficients
import OAI.Hierarchy.ABPFirstCutRegroup
import OAI.Hierarchy.SlotCoefficientClosure

namespace OAI
/-! # Formula partitions on the physical legs of a graph tensor

For each vertex partition a rank term is a product over its blocks. Giving a
block the physical legs of all its vertices lets it recover precisely the slot
arguments of the original factor. The grouped rank bound for each partition
therefore applies directly to the equality wires used for spectral pricing.
-/

namespace Hierarchy.FormulaPartitionRank

open ABPFirstCut Computability.BorderVNP
open scoped Classical BigOperators
noncomputable section

variable {V P J C : Type} {τ : V → Type} {ν : P → Type} {F : Type*} [Field F]

private def readBlock (owner : P → V)
    (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    {B : ℕ} (π : Partition V B) (j : Fin B)
    (x : (p : {p // π.val (owner p) = j}) → ν p.val) : Fiber τ π j :=
  fun v => assemble v.val (fun p => x ⟨p.val, (congrArg π.val p.property).trans v.property⟩)

variable [Fintype V]

/-- The admissible partitions depend on the slot set and its size, so the
same finite index can be used for every approximating formula. -/
abbrev Admissible (V : Type) [Fintype V] :=
  ↥(FormulaPartition.admissiblePartitions V (Nat.log 2 (Fintype.card V)))

theorem card_admissible (V : Type) [Fintype V] :
    Fintype.card (Admissible V) ≤ 2 ^ (2 * Fintype.card V) := by
  simpa only [Admissible, Fintype.card_coe] using FormulaPartition.card_admissiblePartitions V
    (Nat.log 2 (Fintype.card V))

/-- A uniform block-product expansion survives border projection and splitting slots into legs. -/
theorem border_formula_partition_of_expansion [Fintype C]
    (owner : P → V) (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    {B R s : ℕ} (shape : C → Partition V B)
    (hexact : ∀ p : MvPolynomial (Σ v, τ v) (AlgebraicClosure F), HasFormula s p →
      ∃ g : (c : C) → Fin R → (j : Fin B) → Fiber τ (shape c) j → AlgebraicClosure F,
        ∀ a, slotCoeff a Finset.univ p = ∑ c, ∑ r, ∏ j, g c r j (restrict (shape c) j a))
    {f : MvPolynomial (Σ v, τ v) F} (hp : DegreeBorderAtMost HasFormula (Fintype.card V) s f) :
    (fun x => slotCoeff (slotRead owner assemble x) Finset.univ
      (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f)) ∈
    imageClosure (partitionRankSums (fun c p => (shape c).val (owner p)) R) := by
  apply degreeModelClosure_readSlots (slotRead owner assemble) HasFormula _ _ hp
  intro p h
  obtain ⟨g, heq⟩ := hexact p h
  exact mem_partitionRankSums_of_expansion _ _ _
    (fun c r j x => g c r j (readBlock owner assemble (shape c) j x))
    (fun x => heq (slotRead owner assemble x))

end
end Hierarchy.FormulaPartitionRank

namespace Hierarchy.IncidenceGraph

open ABPFirstCut Computability.BorderVNP FormulaPartitionRank
open scoped Classical

/-- The physical coefficient projection of the graph polynomial is its tensor of equality wires. -/
theorem slotRead_wire_eq (G : IncidenceGraph) (F : Type*) [Field F] (q : ℕ) :
    (fun x => slotCoeff (slotRead G.portOwner (G.portAssemble (q := q)) x) Finset.univ
      (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (G.contraction F q))) =
      (equalityWireRaw G.E (AlgebraicClosure F) q).coeff := by
  funext x
  exact G.map_slotCoeff_portAssignment (algebraMap F (AlgebraicClosure F)) x

end Hierarchy.IncidenceGraph

end OAI
