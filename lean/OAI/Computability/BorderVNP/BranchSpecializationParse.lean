import OAI.Computability.BorderVNP.BranchSpecializationClosure
import OAI.Computability.BorderVNP.BranchSpecializationBits
import OAI.Computability.BorderVNP.ParseTable

/-!
# Specialization of the actual universal parse table

A border circuit for an integral input polynomial puts its entire degree-component
vector in the closure of the table image over the algebraic closure of the ground
field. The degrees and binary coefficient heights needed in Section 9 come from
the integral parse counts of Section 2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseTable

open MvPolynomial VPVNP BranchSpecialization

/-- Polynomial bound on the binary logarithm of the integral coordinate norm in
the table of degree `k + 1`, with `v` variables and gate budget `s`. -/
def tableHeightExponent (v k s : ℕ) : ℕ :=
  2 * k + (v + s + 1) * (2 * k) + v * (k + 1)

/-- Every entry of the universal coefficient map has parameter degree at most
twice the output degree minus one. -/
theorem table_degree_le (V : Type*) [Fintype V] (k s : ℕ) (e : DegreeMonomial V (k + 1)) :
    (table V k s e).totalDegree ≤ 2 * k + 1 :=
  coordinate_degree (Fin.last k) (0 : State V s) e.val

/-- The binary coefficient height bound follows from counting all ordered parses,
including the terms of the table for monomials with repeated variables. -/
theorem table_norm_le (V : Type*) [Fintype V] (k s : ℕ) (e : DegreeMonomial V (k + 1)) :
    coefficientNorm (table V k s e) ≤ 2 ^ tableHeightExponent (Fintype.card V) k s := by
  have h := coordinate_norm_le (Fin.last k) (0 : State V s) e.val
  rw [← intCast_coefficientNorm] at h
  have h' : coefficientNorm (table V k s e) ≤
      4 ^ k * (Fintype.card V + s + 1) ^ (2 * k) * Fintype.card V ^ (k + 1) := by
    simpa only [table, State, Fintype.card_fin, Fin.val_last] using Int.ofNat_le.mp h
  calc
    _ ≤ _ := h'
    _ ≤ 4 ^ k * (2 ^ (Fintype.card V + s + 1)) ^ (2 * k) *
          (2 ^ Fintype.card V) ^ (k + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _))
        (Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _)
    _ = _ := by simp only [tableHeightExponent, pow_add, pow_mul]; norm_num

/-- A geometric border circuit over any ground field gives the image-closure
hypothesis of Section 9 with the integral coefficient vector of the input. -/
theorem tableClosure_of_borderApprox_int {F V : Type*} [Field F] [Fintype V]
    (p : MvPolynomial V ℤ) (k s : ℕ)
    (hp : BorderApprox (k + 1) s (map (Int.castRingHom F) p)) :
    Int.castRingHom (AlgebraicClosure F) ∘ coeffVector (k + 1) p ∈ imageClosure
      (polynomialImage (fun i => map (Int.castRingHom (AlgebraicClosure F)) (table V k s i))) := by
  have hc : (algebraMap F (AlgebraicClosure F)).comp (Int.castRingHom F) =
      Int.castRingHom (AlgebraicClosure F) := Subsingleton.elim _ _
  rw [BorderApprox, map_map, hc] at hp
  have h := geometricApprox_mem_tableClosure V hp
  simpa only [polynomialImage, coeffVector_map, eval_map] using h

/-- Explicit binary exponent for a prime preserving the universal table closure,
including an exclusion integer with `e`-bit absolute value. -/
noncomputable def tablePrimeExponent (V : Type*) [Fintype V] (k s e : ℕ) : ℕ :=
  let h := Fintype.card (GrammarLabel V (State V s) (k + 1))
  let d := 2 * k + 1
  primeExponent h d (separatingDegree h d) (tableHeightExponent (Fintype.card V) k s) e

/-- With a characteristic-zero border circuit, the entire reduced degree-component
vector lies in the image closure of the universal table at a prime avoiding the
fixed bad denominators. The same prime works for every infinite extension. -/
theorem exists_prime_preserving_tableClosure {F V : Type*} [Field F] [CharZero F] [Fintype V]
    (p : MvPolynomial V ℤ) (k s e : ℕ) (z : ℤ) (hz : z ≠ 0) (he : z.natAbs ≤ 2 ^ e)
    (hp : BorderApprox (k + 1) s (map (Int.castRingHom F) p)) :
    ∃ t : ℕ, t.Prime ∧ t ≤ 2 ^ tablePrimeExponent V k s e ∧ ¬ (t : ℤ) ∣ z ∧
      ∀ (K : Type*) [Field K] [CharP K t] [Infinite K],
        Int.castRingHom K ∘ coeffVector (k + 1) p ∈ imageClosure (polynomialImage
          (fun i => map (Int.castRingHom K) (table V k s i))) :=
  exists_prime_preserving_imageClosure (E := AlgebraicClosure F) (table V k s)
    (coeffVector (k + 1) p) _ _ e z hz he (table_degree_le V k s) (table_norm_le V k s)
    (tableClosure_of_borderApprox_int p k s hp)

/-- The prime has polynomial bit length in the Section 9 parameter whenever
the number of variables, output degree, gate budget and exclusion bit length
are polynomially bounded in that parameter. -/
theorem polynomiallyBounded_tablePrimeExponent {V : ℕ → Type*} [∀ n, Fintype (V n)]
    {k s e : ℕ → ℕ} (hv : PolynomiallyBounded fun n => Fintype.card (V n))
    (hk : PolynomiallyBounded k) (hs : PolynomiallyBounded s) (he : PolynomiallyBounded e) :
    PolynomiallyBounded fun n => tablePrimeExponent (V n) (k n) (s n) (e n) := by
  have ht := (hv.add hs).add (.const 1)
  have hh := ((ht.mul hv).add (((hk.add (.const 1)).pow 2).mul (ht.pow 3))).of_le
    (fun n => parameter_count_le (V n) (k n) (s n))
  have h2 := (PolynomiallyBounded.const 2).mul hk
  have hd := h2.add (.const 1)
  have hb := (h2.add (ht.mul h2)).add (hv.mul (hk.add (.const 1)))
  exact polynomiallyBounded_perron_primeExponent hh hd.clog hb.clog he.clog

/-- A single polynomial bounds the prime bit length for all parse tables whose
individual numeric parameters are at most `M`. The table may be chosen
nonuniformly, and the sizes `M` need not run through all natural numbers. -/
theorem exists_uniform_tablePrimeExponent_bound :
    ∃ A C : ℕ, ∀ (V : Type*) [Fintype V] (k s e M : ℕ),
      Fintype.card V ≤ M → k ≤ M → s ≤ M → e ≤ M → tablePrimeExponent V k s e ≤ A * (M + 1) ^ C := by
  let states (M : ℕ) := M + M + 1
  let count (M : ℕ) := states M * M + (M + 1) ^ 2 * states M ^ 3
  let degree (M : ℕ) := 2 * M + 1
  let cost (M : ℕ) := primeExponent (count M) (degree M) (separatingDegree (count M) (degree M))
    (tableHeightExponent M M M) M
  have hi := PolynomiallyBounded.id
  have hs := (hi.add hi).add (.const 1)
  have hh := (hs.mul hi).add (((hi.add (.const 1)).pow 2).mul (hs.pow 3))
  have ht := (PolynomiallyBounded.const 2).mul hi
  have hcost : PolynomiallyBounded cost := polynomiallyBounded_perron_primeExponent hh
    (ht.add (.const 1)).clog ((ht.add (hs.mul ht)).add (hi.mul (hi.add (.const 1)))).clog hi.clog
  obtain ⟨A, C, hAC⟩ := hcost.exists_global_bound
  refine ⟨A, C, fun V _ k s e M hv hk hs he => LE.le.trans ?_ (hAC M)⟩
  let h := Fintype.card (GrammarLabel V (State V s) (k + 1))
  have hcard : h ≤ count M := (parameter_count_le V k s).trans (by dsimp [count, states]; gcongr)
  have hdeg : 2 * k + 1 ≤ degree M := by dsimp [degree]; omega
  have hsep : separatingDegree h (2 * k + 1) ≤ separatingDegree (count M) (degree M) := by
    dsimp [separatingDegree, RadicalCertificate.perronSimplexBound, RadicalCertificate.perronRadius]
    gcongr
    omega
  have hheight : tableHeightExponent (Fintype.card V) k s ≤ tableHeightExponent M M M := by
    dsimp [tableHeightExponent]
    gcongr
  change primeExponent h (2 * k + 1) (separatingDegree h (2 * k + 1)) _ _ ≤ _
  dsimp only [cost, primeExponent]
  gcongr

end ParseTable

end BorderVNP
end Computability
end OAI
