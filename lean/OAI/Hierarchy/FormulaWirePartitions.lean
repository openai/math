import OAI.Hierarchy.FormulaPartitions
import OAI.Hierarchy.FormulaBlockRegroup

namespace OAI
/-! # Formula partition rank of the physical wire tensor -/

namespace Hierarchy.FormulaPartitionRank

open ABPFirstCut Computability.BorderVNP
open scoped Classical BigOperators
noncomputable section

variable {V P : Type} {τ : V → Type} {ν : P → Type} {F : Type*} [Field F] [Fintype V]

/-- Coefficient projection and splitting slots into legs preserve the distinct
partitions and the polynomial bound on the number of products per partition. -/
theorem border_formula_partition_on_legs
    (owner : P → V) (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    {f : MvPolynomial (Σ v, τ v) F} {s : ℕ} (hd : 2 ≤ Fintype.card V)
    (hp : DegreeBorderAtMost HasFormula (Fintype.card V) s f) :
    (fun x => slotCoeff (slotRead owner assemble x) Finset.univ
      (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f)) ∈
    imageClosure (partitionRankSums (fun (π : Partition V (Nat.log 2 (Fintype.card V) + 1)) p =>
      π.val (owner p)) ((s+2)^24)) :=
  border_formula_partition_of_expansion owner assemble id
    (fun _ h => FormulaPartition.hasFormula_factorization h hd) hp

/-- The quantitative decomposition uses at most `2^(2*d)` partitions for
`d` slots, with the same number of block products per partition. -/
theorem border_formula_admissible_on_legs
    (owner : P → V) (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    {f : MvPolynomial (Σ v, τ v) F} {s : ℕ} (hd : 2 ≤ Fintype.card V)
    (hp : DegreeBorderAtMost HasFormula (Fintype.card V) s f) :
    (fun x => slotCoeff (slotRead owner assemble x) Finset.univ
      (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f)) ∈
    imageClosure (partitionRankSums (fun (π : Admissible V) p => π.val.val (owner p)) ((s+2)^24)) := by
  apply border_formula_partition_of_expansion owner assemble (fun π : Admissible V => π.val) _ hp
  intro p h
  obtain ⟨g, heq⟩ := FormulaPartition.hasFormula_admissible_factorization h hd
  refine ⟨fun c => g c.val, fun a => ?_⟩
  exact (heq a).trans (Finset.sum_coe_sort
    (FormulaPartition.admissiblePartitions V (Nat.log 2 (Fintype.card V)))
    (fun π => ∑ r, ∏ j, g π r j (restrict π j a))).symm

end
end Hierarchy.FormulaPartitionRank

namespace Hierarchy.IncidenceGraph

open ABPFirstCut Computability.BorderVNP FormulaPartitionRank
open scoped Classical

set_option maxHeartbeats 1000000 in
/-- The graph contraction of border formula size `s` gives equality wires in
the closure of sums over vertex partitions, with grouped rank `(s+2)^24`. -/
theorem border_formula_wire_partition_sums (G : IncidenceGraph) (F : Type*) [Field F]
    {q s : ℕ} (hd : 2 ≤ Fintype.card G.V)
    (hp : DegreeBorderAtMost HasFormula (Fintype.card G.V) s (G.contraction F q)) :
    (equalityWireRaw G.E (AlgebraicClosure F) q).coeff ∈
    imageClosure (partitionRankSums
      (fun (π : Partition G.V (Nat.log 2 (Fintype.card G.V) + 1)) p => π.val (G.portOwner p))
      ((s+2)^24)) := by
  rw [← slotRead_wire_eq G F q]
  exact border_formula_partition_on_legs (V := G.V) (P := G.E × Bool) (F := F)
    (τ := fun v => G.Incident v → Fin q) (ν := fun _ => Fin q) (f := G.contraction F q) (s := s)
    G.portOwner (G.portAssemble (q := q)) hd hp

set_option maxHeartbeats 1000000 in
/-- The physical wire decomposition with at most `2^(2*d)` summands, where
`d` is the number of vertices. -/
theorem border_formula_wire_admissible_sums (G : IncidenceGraph) (F : Type*) [Field F]
    {q s : ℕ} (hd : 2 ≤ Fintype.card G.V)
    (hp : DegreeBorderAtMost HasFormula (Fintype.card G.V) s (G.contraction F q)) :
    (equalityWireRaw G.E (AlgebraicClosure F) q).coeff ∈ imageClosure (partitionRankSums
      (fun (π : Admissible G.V) p => π.val.val (G.portOwner p)) ((s+2)^24)) := by
  rw [← slotRead_wire_eq G F q]
  exact border_formula_admissible_on_legs (V := G.V) (P := G.E × Bool) (F := F)
    (τ := fun v => G.Incident v → Fin q) (ν := fun _ => Fin q) (f := G.contraction F q) (s := s)
    G.portOwner (G.portAssemble (q := q)) hd hp


end Hierarchy.IncidenceGraph

end OAI
