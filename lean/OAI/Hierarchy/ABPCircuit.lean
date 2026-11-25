import OAI.Hierarchy.Models
import OAI.Hierarchy.ABPCircuitBuilder
import OAI.Computability.VPVNP.PolynomialBounds

namespace OAI
/-! # Simulating an algebraic branching program by an arithmetic circuit

Each processed vertex keeps a reference to its path sum. The program computes the affine
label and one weighted contribution for each incoming edge, retaining all earlier references.
-/

namespace Hierarchy
open Computability.VPVNP MvPolynomial
open scoped BigOperators
noncomputable section

variable {F : Type*} {σ : Type} [Field F] [Fintype σ]

/-- An affine form in `k` variables can be computed with at most `2*k+1` gates. -/
theorem Affine.circuitSize_le (a : Affine F σ) :
    circuitSize a.polynomial ≤ 2 * Fintype.card σ + 1 := by
  classical
  have sumBound (s : Finset σ) :
      circuitSize (∑ i ∈ s, C (a.coeff i) * X i) ≤ 2 * s.card := by
    induction s using Finset.induction_on with
    | empty =>
      simpa using (circuitSize_C (σ := σ) (0 : F)).le
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
      have term := circuitSize_binOp_le .mul (C (a.coeff i)) (X i)
      change circuitSize (C (a.coeff i) * X i) ≤ _ at term
      simp only [circuitSize_C, circuitSize_X] at term
      have added := circuitSize_binOp_le .add (C (a.coeff i) * X i)
        (∑ k ∈ s, C (a.coeff k) * X k)
      change circuitSize (_ + _) ≤ _ at added
      omega
  have added := circuitSize_binOp_le .add (C a.constant)
    (∑ i, C (a.coeff i) * X i)
  change circuitSize a.polynomial ≤ _ at added
  rw [circuitSize_C, zero_add] at added
  exact added.trans (Nat.add_le_add_right (sumBound Finset.univ) 1)

/-- All path sums through the current vertex are held simultaneously in one circuit
program. The bound charges each edge once and allows vertices of arbitrary fan-out. -/
theorem Rows.program {n : ℕ} (g : Rows F σ n) :
    ∃ k ≤ g.edgeCount * (2 * Fintype.card σ + 3),
      ∃ (p : Program F σ k) (ref : Fin n → Ref F σ k),
        ∀ i, (Circuit.mk p (ref i)).polynomial = g.values i := by
  classical
  induction g with
  | source =>
    refine ⟨0, Nat.zero_le _, .nil, fun _ => .const 1, ?_⟩
    intro i
    change C (1 : F) = 1
    exact map_one _
  | @snoc n prev edges ih =>
    obtain ⟨k, bound, p, ref, reads⟩ := ih
    let terms : List (Ref F σ k × MvPolynomial σ F) :=
      edges.map (fun e => (ref e.1, e.2.polynomial))
    have cost : ∀ e ∈ terms, circuitSize e.2 ≤ 2 * Fintype.card σ + 1 := by
      intro e he
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
      exact f.2.circuitSize_le
    obtain ⟨m, work, q, lift, last, keep, final⟩ := CircuitBuilder.extendPaths p terms
      (2 * Fintype.card σ + 1) cost
    refine ⟨m, ?_, q, Fin.lastCases last (fun i => lift (ref i)), ?_⟩
    · have len : terms.length = edges.length := by simp [terms]
      rw [len] at work
      change m ≤ (prev.edgeCount + edges.length) * _
      rw [Nat.add_mul]
      have factor : 2 * Fintype.card σ + 1 + 2 = 2 * Fintype.card σ + 3 := by omega
      rw [factor] at work
      omega
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [Rows.values, terms, List.map_map, Function.comp_def, reads] using final
      · simpa [Rows.values] using (keep (ref j)).trans (reads j)

/-- Formal-polynomial simulation of an arbitrary topologically ordered affine ABP. -/
theorem ABP.circuitSize_le (g : ABP F σ) :
    circuitSize g.polynomial ≤ g.size * (2 * Fintype.card σ + 3) := by
  obtain ⟨k, bound, p, ref, reads⟩ := g.rows.program
  apply circuitSize_le_iff.mpr
  refine ⟨k, bound.trans (Nat.mul_le_mul_right _ ?_), ⟨p, ref g.sink⟩, reads g.sink⟩
  change g.rows.edgeCount ≤ g.vertices + g.rows.edgeCount
  omega

theorem IsVBP.isVP {τ : ℕ → Type} [∀ n, Fintype (τ n)] {p : Family F τ}
    (h : IsVBP p) : IsVP p := by
  obtain ⟨family, g, computes, cost⟩ := h
  refine ⟨family, ?_⟩
  apply PolynomiallyBounded.of_le
    (cost.mul (((PolynomiallyBounded.const 2).mul family.1).add (PolynomiallyBounded.const 3)))
  intro n
  rw [← computes n]
  exact (g n).circuitSize_le


end
end Hierarchy

end OAI
