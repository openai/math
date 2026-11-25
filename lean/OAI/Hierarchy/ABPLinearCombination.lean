import OAI.Hierarchy.ABPCopy

namespace OAI
/-! # Linear combinations of affine branching programs

The summands share one source. Each copied sink receives an edge to a final vertex whose
label is the coefficient of that summand. Vertices of an earlier summand stay available
when a later summand is copied.
-/

namespace Hierarchy
open MvPolynomial
open scoped BigOperators
noncomputable section

variable {F : Type*} {σ : Type} {ι : Type*} [Field F] [Fintype σ]

private theorem linearRows (S : Finset ι) (c : ι → F) (G : ι → ABP F σ) (s : ℕ) :
    (∀ t ∈ S, (G t).size ≤ s) → ∀ {n : ℕ} (g : Rows F σ n) (v : Fin n),
      ∃ (m : ℕ) (h : n ≤ m) (out : Rows F σ m) (edges : List (Fin m × Affine F σ)),
        (∀ i : Fin n, out.values (i.castLE h) = g.values i) ∧
        edges.length = S.card ∧
        (edges.map (fun e => out.values e.1 * e.2.polynomial)).sum =
          g.values v * ∑ t ∈ S, C (c t) * (G t).polynomial ∧
        m + out.edgeCount ≤ n + g.edgeCount + S.card * s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ n g v
    exact ⟨n, le_rfl, g, [], fun _ => rfl, by simp, by simp, by simp⟩
  | @insert t S ht ih =>
    intro bound n g v
    have firstSize := bound t (Finset.mem_insert_self t S)
    obtain ⟨a, h₁, first, sink, keep₁, firstValue, firstCost⟩ := (G t).copyFrom g v
    obtain ⟨b, h₂, out, tail, keep₂, tailLength, tailValue, tailCost⟩ :=
      ih (fun i hi => bound i (Finset.mem_insert_of_mem hi)) first (v.castLE h₁)
    refine ⟨b, h₁.trans h₂, out, (sink.castLE h₂, .ofScalar (c t)) :: tail, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (keep₂ (i.castLE h₁)).trans (keep₁ i)
    · simp [tailLength, ht]
    · simp only [List.map_cons, List.sum_cons, Affine.polynomial_ofScalar, keep₂, firstValue,
        tailValue, keep₁, Finset.sum_insert ht, mul_add]
      ac_rfl
    · rw [Finset.card_insert_of_notMem ht, Nat.add_mul, Nat.one_mul]
      omega

/-- A linear combination of `k` size-`s` branching programs uses at most
`k * (s+1) + 2` vertices and edges. -/
theorem ABP.linearCombination (S : Finset ι) (c : ι → F) (G : ι → ABP F σ) (s : ℕ)
    (bound : ∀ t ∈ S, (G t).size ≤ s) :
    HasABP (S.card * (s + 1) + 2) (∑ t ∈ S, C (c t) * (G t).polynomial) := by
  obtain ⟨m, _, out, edges, _, len, value, cost⟩ :=
    linearRows S c G s bound (.source : Rows F σ 1) 0
  refine ⟨⟨m + 1, out.snoc edges, Fin.last m⟩, ?_, ?_⟩
  · simpa [ABP.polynomial, Rows.values] using value
  · change m + 1 + (out.edgeCount + edges.length) ≤ _
    change m + out.edgeCount ≤ 1 + 0 + S.card * s at cost
    rw [len, Nat.mul_add, Nat.mul_one]
    omega

end
end Hierarchy

end OAI
