import OAI.Computability.VPVNP.Classes
import OAI.Computability.VPVNP.HamiltonianPadding
import OAI.Computability.VPVNP.PermanentPadding

/-!
# Exact circuit sizes of the complete families under padding

The projections of §15.1 make exact circuit size monotone in matrix order. The
transfer theorem takes as inputs the lower bound for the hard family and its
p-projection from the matrix family. It covers every sufficiently large order,
including the gaps between consecutive orders in the reduction.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {R : Type*} [CommRing R]

/-- Diagonal padding makes minimum permanent circuit size nondecreasing. -/
theorem permanentCircuitSize_le_succ (m : ℕ) :
    circuitSize (permanentPolynomial R m) ≤ circuitSize (permanentPolynomial R (m + 1)) := by
  rw [← permanentPadding_polynomial R m]
  exact circuitSize_projection_le _ _

/-- Forced-arc subdivision makes minimum Hamiltonian-cycle circuit size
nondecreasing from order two onwards. -/
theorem hamiltonianCircuitSize_le_succ {m : ℕ} (hm : 2 ≤ m) :
    circuitSize (hamiltonianCyclePolynomial R m) ≤
      circuitSize (hamiltonianCyclePolynomial R (m + 1)) := by
  let a : Fin m := ⟨0, by omega⟩
  have h : (cyclePaddingProjection R a).hom (hamiltonianCyclePolynomial R (m + 1)) =
      hamiltonianCyclePolynomial R m := hamiltonianCyclePolynomial_pad hm a
  rw [← h]
  exact circuitSize_projection_le _ _

/-- Given a polynomially bounded sequence of projection orders and an eventual
hardness bound, monotone padding transfers the bound to all large matrix orders. -/
private theorem matrixFamily_bound_of_projections {ι : ℕ → Type*}
    (hard : (n : ℕ) → MvPolynomial (ι n) R)
    (matrixFamily : (m : ℕ) → MvPolynomial (Fin m × Fin m) R)
    {q : ℕ → ℕ} {A b n₀ : ℕ} (hA : 0 < A) (hb : 0 < b)
    (hhard : EventuallySuperpolynomial fun n => circuitSize (hard n))
    (horder : ∀ n ≥ n₀, q n ≤ A * n ^ b)
    (hproj : ∀ n ≥ n₀, ∃ φ : Projection R (Fin (q n) × Fin (q n)) (ι n),
      φ.hom (matrixFamily (q n)) = hard n)
    (hstep : ∀ m ≥ 2, circuitSize (matrixFamily m) ≤ circuitSize (matrixFamily (m + 1)))
    (C : ℕ) : ∃ M : ℕ, ∀ m ≥ M, m ^ C < circuitSize (matrixFamily m) := by
  obtain ⟨N, hN⟩ := hhard 1 le_rfl
  let S := max (circuitSize (matrixFamily 0)) (circuitSize (matrixFamily 1))
  refine eventualBound_of_polynomialProjection (q := q) (n₀ := max (max n₀ N) S)
    hA hb hhard ?_ hstep C
  intro n hn
  have hn₀ : n₀ ≤ n := ((le_max_left ..).trans (le_max_left ..)).trans hn
  have hnN : N ≤ n := ((le_max_right ..).trans (le_max_left ..)).trans hn
  have hnS : S ≤ n := (le_max_right ..).trans hn
  obtain ⟨φ, hφ⟩ := hproj n hn₀
  have hsize : circuitSize (hard n) ≤ circuitSize (matrixFamily (q n)) :=
    hφ ▸ circuitSize_projection_le φ _
  refine ⟨?_, horder n hn₀, hsize⟩
  have hbig : S < circuitSize (matrixFamily (q n)) :=
    hnS.trans_lt ((by simpa using hN n hnN : n < circuitSize (hard n)).trans_le hsize)
  by_contra! hsmall
  obtain h | h : q n = 0 ∨ q n = 1 := by omega
  · rw [h] at hbig
    exact hbig.not_ge (le_max_left ..)
  · rw [h] at hbig
    exact hbig.not_ge (le_max_right ..)

variable {F : Type*} [Field F] {ι : ℕ → Type} {hard : Family F ι}

/-- A p-projection onto an eventually hard family forces the same type of bound
at every sufficiently large order of the source family, provided it admits padding. -/
theorem matrixFamily_bound_of_pProjects
    (source : Family F fun m => Fin m × Fin m) (hproj : PProjects hard source)
    (hhard : EventuallySuperpolynomial fun n => circuitSize (hard n))
    (hstep : ∀ m ≥ 2, circuitSize (source m) ≤ circuitSize (source (m + 1)))
    (C : ℕ) : ∃ M : ℕ, ∀ m ≥ M, m ^ C < circuitSize (source m) := by
  obtain ⟨q, ⟨A, b, N, hq⟩, hφ⟩ := hproj
  refine matrixFamily_bound_of_projections hard source (q := q) (n₀ := max 1 N)
    (Nat.zero_lt_succ A) (Nat.zero_lt_succ b) hhard ?_ (fun n _ => hφ n) hstep C
  intro n hn
  refine (hq n ((le_max_right ..).trans hn)).trans ?_
  exact Nat.mul_le_mul (Nat.le_succ A)
    (Nat.pow_le_pow_right ((le_max_left ..).trans hn) (Nat.le_succ b))

/-- The Hamiltonian-cycle implication in §15.1, with the Valiant reduction and
the hard-family lower bound supplied explicitly. -/
theorem hamiltonian_bound_of_pProjects (hproj : PProjects hard (hamiltonianCyclePolynomial F))
    (hhard : EventuallySuperpolynomial fun n => circuitSize (hard n)) (C : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, m ^ C < circuitSize (hamiltonianCyclePolynomial F m) :=
  matrixFamily_bound_of_pProjects _ hproj hhard (fun _ hm => hamiltonianCircuitSize_le_succ hm) C

/-- The permanent implication in §15.1. Its use outside characteristic two
requires the p-projection supplied there by Valiant completeness. -/
theorem permanent_bound_of_pProjects (hproj : PProjects hard (permanentPolynomial F))
    (hhard : EventuallySuperpolynomial fun n => circuitSize (hard n)) (C : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, m ^ C < circuitSize (permanentPolynomial F m) :=
  matrixFamily_bound_of_pProjects _ hproj hhard (fun m _ => permanentCircuitSize_le_succ m) C

end VPVNP
end Computability
end OAI
