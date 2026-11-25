import OAI.LinearAlgebra.SpectralBooks.IndependentSetHardness

/-! # Hard families obtained by projections of directed Hamiltonian cycles -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace IndependentSetGraph
open Filter
open scoped Classical BigOperators

/-- At positive order the subtype of Hamiltonian permutations equals the filtered
permutation sum using the nonempty spanning-cycle convention. -/
theorem hamiltonianCyclePolynomial_eq_spanning (R : Type*) [CommSemiring R] {m : ℕ} (hm : 0 < m) :
    hamiltonianCyclePolynomial R m =
      ∑ p ∈ Finset.univ.filter (fun p : Equiv.Perm (Fin m) => 0 < m ∧ p.IsCycleOn Set.univ),
        ∏ i : Fin m, MvPolynomial.X (i,p i) := by
  exact (Finset.sum_subtype (p:=fun p : Equiv.Perm (Fin m) => p.IsCycleOn Set.univ)
    (Finset.univ.filter (fun p : Equiv.Perm (Fin m) => 0 < m ∧ p.IsCycleOn Set.univ))
    (fun _ => by simp [hm])
    (fun p : Equiv.Perm (Fin m) => ∏ i : Fin m, MvPolynomial.X (R:=R) (i,p i))).symm

/-- Composing any polynomially bounded family of Hamiltonian projections with
the signed independent-set gadgets supplies grids of every sufficiently large order. -/
theorem gridProjections_of_hamiltonian {F : Type*} [Field F] {σ : ℕ → Type*}
    (f : (n : ℕ) → MvPolynomial (σ n) F) (j : ℕ → ℕ) (hj : ∀ n, 2 ≤ j n)
    {A b : ℕ} (size : ∀ᶠ n : ℕ in atTop, j n ^ 3 + j n + 25 * (j n ^ 6 + j n ^ 3) ≤ A*n^b)
    (projection : ∀ n, ∃ p : (Fin (j n) × Fin (j n)) → ProjectionAtom F (σ n),
      project p (hamiltonianCyclePolynomial F (j n)) = f n) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ᶠ n : ℕ in atTop,
      ∀ N : ℕ, C*n^d ≤ N → Nonempty (GridProjection F (σ n) (f n) N) := by
  refine ⟨A+1,b+1,Nat.succ_pos _,Nat.succ_pos _,?_⟩
  filter_upwards [size,eventually_ge_atTop 1] with n hn hpos
  intro N hN
  have hbound : A*n^b ≤ (A+1)*n^(b+1) :=
    Nat.mul_le_mul (Nat.le_succ A) (Nat.pow_le_pow_right hpos (Nat.le_succ b))
  obtain ⟨grid⟩ := exists_gridProjection_of_hamiltonian F (hj n) (hn.trans (hbound.trans hN))
  obtain ⟨p,hp⟩ := projection n
  rw [← hp]
  exact ⟨grid.project p⟩

end IndependentSetGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
