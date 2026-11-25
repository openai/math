import OAI.LinearAlgebra.FiniteFourier.BoundedElimination
import OAI.LinearAlgebra.FiniteFourier.ProtectedCyclotomicRoots
import OAI.LinearAlgebra.FiniteFourier.SemilocalPivot

/-! # Bounded factorization by invertible-coefficient shears

Mapping the two protected elimination words into the cyclotomic ring allows
each coefficient to split as a sum of two units. This gives at most four
times the square of the local dimension many unit shears. -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Matrix.TransvectionStruct

private theorem map_shear_word_with_unit_coefficients {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (f : R →+* S) (split : ∀ x : S, ∃ t, IsUnit t ∧ IsUnit (x - t))
    (L : List (TransvectionStruct I R)) :
    ∃ T : List (TransvectionStruct I S), T.length = 2 * L.length ∧ (∀ t ∈ T, IsUnit t.c) ∧
      f.mapMatrix (L.map toMatrix).prod = (T.map toMatrix).prod := by
  induction L with
  | nil => exact ⟨[], by simp⟩
  | cons t L ih =>
    obtain ⟨T, hl, hu, hT⟩ := ih
    obtain ⟨a, ha, hb⟩ := split (f t.c)
    let b := f t.c - a
    let A : TransvectionStruct I S := ⟨t.i, t.j, t.hij, a⟩
    let B : TransvectionStruct I S := ⟨t.i, t.j, t.hij, b⟩
    refine ⟨A :: B :: T, by simp [hl]; omega, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hb
      exact hu _ hz
    · simp only [List.map_cons, List.prod_cons, map_mul, hT, ← Matrix.mul_assoc]
      congr 1
      change f.mapMatrix (transvection t.i t.j t.c) =
        transvection t.i t.j a * transvection t.i t.j b
      rw [transvection_mul_transvection_same _ _ t.hij, show a + b = f t.c by simp [b]]
      ext i j
      simp [transvection, Matrix.single_apply, Matrix.one_apply, apply_ite f]

/-- An integral local matrix splits over a protected coefficient extension, with
uniform length and with every transvection coefficient a unit in the extension. -/
theorem exists_integral_unit_shear_factorization {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {I S : Type*} [Fintype I] [DecidableEq I] [CommRing S] [Algebra (protectedRationals P) S]
    (split : ∀ x : S, ∃ t, IsUnit t ∧ IsUnit (x-t)) (M : Matrix I I ℤ) :
    ∃ (L L' : List (TransvectionStruct I S)) (D : I → S),
      L.length + L'.length ≤ 4 * (Fintype.card I) ^ 2 ∧
      (∀ t ∈ L, IsUnit t.c) ∧ (∀ t ∈ L', IsUnit t.c) ∧
      M.map (Int.castRingHom S) = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  let f := algebraMap (protectedRationals P) S
  obtain ⟨L, L', D, hlen, h⟩ := exists_protected_diagonal_shear_factorization hP
    (M.map (Int.castRingHom (protectedRationals P)))
  obtain ⟨T, hl, hu, hT⟩ := map_shear_word_with_unit_coefficients f split L
  obtain ⟨T', hl', hu', hT'⟩ := map_shear_word_with_unit_coefficients f split L'
  refine ⟨T, T', fun i => f (D i), by omega, hu, hu', ?_⟩
  have he := congrArg f.mapMatrix h
  simp only [map_mul, hT, hT'] at he
  simpa [RingHom.mapMatrix_apply, Matrix.map_map, Matrix.diagonal_map (map_zero f),
    Function.comp_def] using he

/-- Each cyclotomic quotient over a protected base ring has finite maximal spectrum. -/
theorem finite_maximalSpectrum_protectedCyclotomic {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    Finite (MaximalSpectrum (ProtectedCyclotomic P n)) := by
  let := finite_maximalSpectrum_protectedRationals hP
  let : Module.Finite (protectedRationals P) (ProtectedCyclotomic P n) :=
    (Polynomial.cyclotomic.monic n _).finite_adjoinRoot
  exact finite_maximalSpectrum_of_finite_algebra (protectedRationals P) _

/-- Over the protected eighth-root extension for odd primes, any coefficient
is a sum of two units, uniformly in the protected set. -/
theorem exists_unit_split_protected_eighth {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hodd : ∀ p ∈ P, Odd p) (x : ProtectedCyclotomic P 8) :
    ∃ t, IsUnit t ∧ IsUnit (x-t) := by
  let := finite_maximalSpectrum_protectedCyclotomic hP 8
  have h₂ : IsUnit (2 : ProtectedCyclotomic P 8) := by
    simpa using protectedCyclotomic_isUnit (L := P) 8 (d := 2) (by decide)
      (fun p hp => Nat.coprime_two_right.mpr (hodd p hp))
  exact exists_unit_split h₂ x

/-- Over the ninth-root extension protecting two, the tautological ninth root
supplies a third residue in every residue field. -/
theorem exists_unit_split_protected_ninth_at_two (x : ProtectedCyclotomic {2} 9) :
    ∃ t, IsUnit t ∧ IsUnit (x-t) := by
  let := finite_maximalSpectrum_protectedCyclotomic (P := {2}) (by simp [Nat.prime_two]) 9
  let := protectedCyclotomic_isDomain {2} 9 (by decide)
  have h₉ : IsUnit (9 : ProtectedCyclotomic {2} 9) := by
    simpa using protectedCyclotomic_isUnit (L := {2}) 9 (d := 9) (by decide)
      (by simpa using (by decide : Nat.Coprime 2 9))
  exact exists_unit_split_of_ninth_root (protectedCyclotomic_primitive {2} 9 (by decide)) h₉ x

end FiniteFourier
end LinearAlgebra
end OAI
