import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Directed Hamiltonian cycles as binary matrices

Section 1.1 of *VP and VNP differ over every field* projects the pair of
variables encoding an edge bit to `(1, X e)`. This gives one monomial for
each accepted adjacency matrix. The identity below identifies their sum,
as a formal polynomial, with the sum indexed by single-cycle permutations.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

/-- The edge polynomial obtained by retaining exactly the variables at true bits. -/
noncomputable def booleanPolynomial {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (u : (E → Bool) → R) : MvPolynomial E R :=
  ∑ x, C (u x) * ∏ e, if x e then X e else 1

/-- The adjacency matrix of the directed edges from each vertex to its image. -/
def permutationEdges {m : ℕ} (π : Equiv.Perm (Fin m)) (e : Fin m × Fin m) : Bool :=
  decide (π e.1 = e.2)

theorem permutationEdges_injective {m : ℕ} :
    Function.Injective (permutationEdges (m := m)) := by
  intro π τ h
  apply Equiv.ext
  intro i
  have hi : τ i = π i := by simpa [permutationEdges] using congrFun h (i, π i)
  exact hi.symm

/-- Single directed cycles on all vertices. A loop is a cycle of order one. -/
noncomputable def spanningCycles (m : ℕ) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter (fun π => 0 < m ∧ π.IsCycleOn Set.univ)

/-- Scan a row for its first edge. The diagonal default is used for an empty row. -/
def rowSuccessor {m : ℕ} (x : Fin m × Fin m → Bool) (i : Fin m) : Fin m :=
  ((List.finRange m).find? (fun j => x (i, j))).getD i

theorem rowSuccessor_permutationEdges {m : ℕ} (π : Equiv.Perm (Fin m)) :
    rowSuccessor (permutationEdges π) = π := by
  funext i
  unfold rowSuccessor
  cases h : (List.finRange m).find? (fun j => permutationEdges π (i, j)) with
  | none =>
    have hn := List.find?_eq_none.mp h (π i) (List.mem_finRange _)
    simp [permutationEdges] at hn
  | some j =>
    have hj := List.find?_some h
    simpa [permutationEdges, eq_comm] using hj

/-- Each row is the graph of its scanned successor,
every column is hit, and all vertices occur in the first `m` steps starting from `root`.
Every quantifier in this Boolean test ranges over the vertices. -/
def acceptsCycleMatrix {m : ℕ} (root : Fin m) (x : Fin m × Fin m → Bool) : Bool :=
  decide ((∀ i j, x (i, j) = decide (rowSuccessor x i = j)) ∧
    (∀ j, ∃ i, rowSuccessor x i = j) ∧
    (∀ j, ∃ k : Fin m, (rowSuccessor x)^[k.val] root = j))

theorem acceptsCycleMatrix_iff {m : ℕ} (root : Fin m) (x : Fin m × Fin m → Bool) :
    acceptsCycleMatrix root x = true ↔ x ∈ (spanningCycles m).image permutationEdges := by
  classical
  rw [acceptsCycleMatrix, decide_eq_true_eq]
  have hm : 0 < m := Nat.zero_lt_of_lt root.isLt
  constructor
  · rintro ⟨hrow, hsurj, hreach⟩
    let π : Equiv.Perm (Fin m) := Equiv.ofBijective (rowSuccessor x)
      ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
    have orbit (i : Fin m) : π.SameCycle root i := by
      obtain ⟨k, hk⟩ := hreach i
      refine ⟨(k.val : ℤ), ?_⟩
      rw [zpow_natCast]
      change (rowSuccessor x)^[k.val] root = i
      exact hk
    have hπ : π.IsCycleOn Set.univ :=
      ⟨π.bijective.bijOn_univ, fun i _ j _ => (orbit i).symm.trans (orbit j)⟩
    refine Finset.mem_image.mpr ⟨π, by simpa [spanningCycles, hm] using hπ, ?_⟩
    funext ⟨i, j⟩
    exact (hrow i j).symm
  · rintro hx
    obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hx
    rw [rowSuccessor_permutationEdges]
    refine ⟨fun _ _ => rfl, π.surjective, ?_⟩
    intro j
    have hcyc : π.IsCycleOn (Finset.univ : Finset (Fin m)) := by
      simpa [spanningCycles, hm] using hπ
    obtain ⟨n, hn, heq⟩ := hcyc.exists_pow_eq (Finset.mem_univ root) (Finset.mem_univ j)
    exact ⟨⟨n, by simpa using hn⟩, by simpa only [Equiv.Perm.coe_pow] using heq⟩

/-- The zero-one coefficient for a deterministic Hamiltonian-cycle predicate. -/
noncomputable def cycleIndicator (R : Type*) [CommSemiring R] (m : ℕ)
    (x : Fin m × Fin m → Bool) : R := by
  classical
  exact if x ∈ (spanningCycles m).image permutationEdges then 1 else 0

theorem cycleIndicator_eq_check (R : Type*) [CommSemiring R] {m : ℕ}
    (root : Fin m) (x : Fin m × Fin m → Bool) :
    cycleIndicator R m x = if acceptsCycleMatrix root x then 1 else 0 := by
  classical
  simp only [cycleIndicator, acceptsCycleMatrix_iff]

/-- The directed Hamiltonian-cycle polynomial in matrix indeterminates. -/
noncomputable def hamiltonianCyclePolynomial (R : Type*) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin m × Fin m) R :=
  ∑ π ∈ spanningCycles m, ∏ i, X (i, π i)

theorem booleanPolynomial_cycleIndicator (R : Type*) [CommSemiring R] (m : ℕ) :
    booleanPolynomial (cycleIndicator R m) = hamiltonianCyclePolynomial R m := by
  classical
  unfold booleanPolynomial cycleIndicator hamiltonianCyclePolynomial
  simp only [apply_ite C, map_one, map_zero, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_ite_mem, Finset.sum_image permutationEdges_injective.injOn]
  apply Finset.sum_congr rfl
  intro π _
  rw [Fintype.prod_prod_type]
  simp [permutationEdges]

end VPVNP
end Computability
end OAI
