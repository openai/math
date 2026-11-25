import OAI.Hierarchy.FormulaPartitionPaths
import OAI.Hierarchy.FormulaPartitionCount
import OAI.Hierarchy.FormulaPartitionMask
import OAI.Hierarchy.FormulaBalance
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Combining the grouped factors from all paths of a balanced formula -/

namespace Hierarchy.FormulaPartition
open ABPFirstCut FormulaPartitionRank
open scoped BigOperators Classical
noncomputable section

variable {V : Type} [Fintype V] {τ : V → Type} {F : Type*} [Field F]

omit [Fintype V] in
/-- The choices of an actual terminal formula leaf and its marked ancestors
have a common bound independent of the number of slots. -/
private theorem count_terms [DecidableEq V] (t : ℕ) (f : Formula F (Σ v,τ v)) :
    Fintype.card ((i : Fin (routes f).length) × Positions t ((routes f).get i).steps.length) ≤
      2^(Formula.depth f) * 2^(Formula.depth f) := by
  classical
  rw [Fintype.card_sigma]
  have maskBound (i : Fin (routes f).length) :
      Fintype.card (Positions t ((routes f).get i).steps.length) ≤ 2^(Formula.depth f) :=
    (card_positions _ _).trans (Nat.pow_le_pow_right (by decide)
      (route_length_le_depth f _ (List.get_mem _ i)))
  calc
    _ ≤ ∑ _i : Fin (routes f).length, 2^(Formula.depth f) :=
      Finset.sum_le_sum (fun i _ => maskBound i)
    _ = (routes f).length * 2^(Formula.depth f) := by simp
    _ ≤ _ := by rw [length_routes]; exact Nat.mul_le_mul_right _ (Formula.cost_succ_le_pow_depth f)

/-- A marked path decomposition for each genuine formula walk gives a common
grouped rank bound for the entire formula. -/
theorem assemble_route_factors {s : ℕ} {p : MvPolynomial (Σ v,τ v) F}
    (size : HasFormula s p)
    (decompose : let t := Nat.log 2 (Fintype.card V)
      ∀ (steps : List (Kernel V τ F)) (tip : Leaf V τ F),
        ∃ fac : Partition V (t+1) → Positions t steps.length → Fin (t+1) → ((v : V) → τ v) → F,
          (∀ π pos j, Depends π j (fac π pos j)) ∧
          (∀ a, run a tip steps Finset.univ = ∑ π, ∑ pos, ∏ j, fac π pos j a) ∧
          (∀ π, π ∉ admissiblePartitions V t → ∀ pos a, (∏ j, fac π pos j a) = 0)) :
    ∃ g : (π : Partition V (Nat.log 2 (Fintype.card V)+1)) → Fin ((s+2)^24) →
        (j : Fin (Nat.log 2 (Fintype.card V)+1)) → Fiber τ π j → F,
      (∀ a, slotCoeff a Finset.univ p = ∑ π, ∑ r, ∏ j, g π r j (restrict π j a)) ∧
      ∀ π, π ∉ admissiblePartitions V (Nat.log 2 (Fintype.card V)) →
        ∀ a, (∑ r, ∏ j, g π r j (restrict π j a)) = 0 := by
  classical
  obtain ⟨f, hf, size⟩ := size
  obtain ⟨b, hb, dep⟩ := Formula.exists_balanced f
  let t := Nat.log 2 (Fintype.card V)
  let P := Partition V (t+1)
  let rs := routes b
  let idx := Fin rs.length
  let path (i : idx) := rs.get i
  let mask (i : idx) := Positions t (path i).steps.length
  let I := (i : idx) × mask i
  have terms : Fintype.card I ≤ (s+2)^24 := by
    have powH := Formula.pow_le_of_log_depth (n := f.cost+2) (by omega) dep
    calc
      _ ≤ 2^b.depth * 2^b.depth := count_terms t b
      _ ≤ (f.cost+2)^12 * (f.cost+2)^12 := Nat.mul_le_mul powH powH
      _ = (f.cost+2)^24 := (pow_add _ 12 12).symm
      _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  choose pieces localPieces expand outside using fun i : idx =>
    decompose (path i).steps (path i).tip
  choose g hg using fun π : P => fixed_partition π
    (fun (i : I) j => pieces i.1 π i.2 j)
    (fun i j => localPieces i.1 π i.2 j) terms
  refine ⟨g,(fun a => ?_),?_⟩
  · rw [← hf, ← hb, slotCoeff_routes]
    have eval : routeSum a rs Finset.univ =
        ∑ i : idx, run a (path i).tip (path i).steps Finset.univ := by
      unfold routeSum
      rw [← Fin.sum_ofFn]
      exact congrArg List.sum (List.ofFn_getElem_eq_map rs (fun r => run a r.tip r.steps Finset.univ)).symm
    rw [eval]
    simp_rw [expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    rw [←hg π a]
    exact (Fintype.sum_sigma (fun z : I => ∏ j, pieces z.1 π z.2 j a)).symm

  · intro π miss a
    rw [← hg π a]
    exact Finset.sum_eq_zero (fun i _ => outside i.1 π miss i.2 a)

end
end Hierarchy.FormulaPartition

end OAI
