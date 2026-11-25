import OAI.LinearAlgebra.SpectralBooks.ParseTable
import OAI.LinearAlgebra.SpectralBooks.ParseSpan
import OAI.LinearAlgebra.SpectralBooks.GateTrim
import OAI.LinearAlgebra.SpectralBooks.SignedWitnessBorder

/-! # Realizing degree components of all bounded circuits by a single parse table -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial
open scoped Classical

noncomputable section
variable {K σ : Type*} [CommRing K] [Fintype σ]

/-- One choice of parameters gives every positive-degree gate component through the cutoff. -/
theorem exists_parseForm_register {r n : ℕ} (p : Program K σ r) :
    ∃ x : ParseParameter n (Fin r) σ → K, ∀ k < n, ∀ g,
      parseForm x k g = homogeneousComponent (k+1) (registerPolynomial p g) := by
  choose lin hlin using exists_parse_linear p
  choose prod hprod using exists_parse_product p
  let x : ParseParameter n (Fin r) σ → K := Sum.elim
    (fun v ↦ lin v.1 v.2)
    (fun ⟨g, d, e, a, b⟩ ↦ if h : e.val < d.val + 1 then prod g d.val (⟨e.val,h⟩,a,b) else 0)
  refine ⟨x, ?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk g
    cases k with
    | zero => exact (parseForm_zero x g).trans (hlin g).symm
    | succ k =>
      rw [parseForm_succ, hprod g k]
      apply Finset.sum_congr rfl
      intro q _
      rcases q with ⟨e,a,b⟩
      have he := e.isLt
      have h₁ : Fin.ofNat (n+1) k = ⟨k, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      have h₂ : Fin.ofNat (n+1) e.val = ⟨e.val, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      dsimp only [Prod.fst, Prod.snd]
      rw [ih _ he (by omega), ih _ (Nat.lt_succ_of_le (Nat.sub_le _ _)) (by omega), h₁, h₂]
      simp only [x, Sum.elim_inr, dite_eq_left he]

/-- The fixed integral degree-`n` parse map evaluated over `F`. The output slot is zero for
every circuit with the given size budget. -/
def parseImage (F σ : Type*) [Field F] [Fintype σ] (n s : ℕ) : Set (DegreeMonomial σ n → F) :=
  Set.range fun x : ParseParameter n (Fin (3*s+3)) σ → F ↦
    fun m ↦ eval₂ (Int.castRingHom F) x (parseCoordinates n (0 : Fin (3*s+3)) m)

/-- The integral table contains every degree component attainable with the gate budget. -/
theorem circuitCoefficientVectors_subset_parseImage (F σ : Type*) [Field F] [Fintype σ]
    {n s : ℕ} (hn : 0 < n) : circuitCoefficientVectors F σ n s ⊆ parseImage F σ n s := by
  rintro v ⟨r, p, o, hs, rfl⟩
  obtain ⟨q, hq⟩ := exists_fixed_register_program p o hs
  obtain ⟨x, hx⟩ := exists_parseForm_register (n := n) q
  refine ⟨x, ?_⟩
  funext m
  change eval₂ (Int.castRingHom F) x (parseCoordinates n (0 : Fin (3*s+3)) m) = _
  rw [eval₂_parseCoordinates (0 : Fin (3*s+3)) m x, hx _ (by omega), show n - 1 + 1 = n by omega, hq]
  exact congrFun (degreeCoefficientVector_homogeneousComponent n (registerPolynomial p o)) m

/-- Small degree-component border size puts the full coefficient vector in the closure of
one polynomial map, uniformly in the circuit topology. -/
theorem DegreeBorderSizeAtMost.mem_parseClosure {F σ : Type*} [Field F] [Fintype σ]
    {n s : ℕ} {f : MvPolynomial σ F} (h : DegreeBorderSizeAtMost n s f) (hn : 0 < n) :
    degreeCoefficientVector n (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) ∈
      zeroLocus (AlgebraicClosure F) (vanishingIdeal (AlgebraicClosure F)
        (parseImage (AlgebraicClosure F) σ n s)) :=
  zeroLocus_anti_mono (vanishingIdeal_anti_mono (circuitCoefficientVectors_subset_parseImage _ _ hn)) h

/-- Every coefficient of the signed witness has one common parse-table border approximation. -/
theorem signedWitness_mem_parseClosure (F : Type*) [Field F] {n s : ℕ}
    (hn : 0 < n) (h : degreeBorderSize n (signedWitnessPolynomial F n) ≤ s) :
    degreeCoefficientVector n (signedWitnessPolynomial (AlgebraicClosure F) n) ∈
      zeroLocus (AlgebraicClosure F) (vanishingIdeal (AlgebraicClosure F)
        (parseImage (AlgebraicClosure F) (Fin n × Bool) n s)) := by
  have hmap : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (signedWitnessPolynomial F n) =
      signedWitnessPolynomial (AlgebraicClosure F) n := by simp [signedWitnessPolynomial]
  exact hmap ▸ ((degreeBorderSize_le_iff n s _).mp h).mem_parseClosure hn

end

end SpectralBooks
end LinearAlgebra
end OAI
