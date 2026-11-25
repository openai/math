import OAI.Computability.BorderVNP.BranchBadLocus

/-! # Common denominators and graph specialization in §9.2

A degree-`e` polynomial in rational chart coordinates with common denominator `u`
has numerator of degree at most `e d` over `u^e`, when all coordinate numerators and
`u` have degree at most `d`. The resulting bad-locus equation specializes to the
whole graph chart, including points where `u` vanishes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

variable {I σ K : Type*} [Field K]

/-- The numerator after substituting chart coordinates with one common denominator
and clearing to a prescribed total degree. -/
noncomputable def clearedSubstitution (den : MvPolynomial σ K) (num : I → MvPolynomial σ K)
    (e : ℕ) (p : MvPolynomial I K) : MvPolynomial σ K :=
  ∑ a ∈ p.support, C (p.coeff a) * (a.prod fun i j => num i ^ j) * den ^ (e-a.degree)

/-- Uniform total-degree bound for a cleared chart numerator. -/
theorem clearedSubstitution_degree (den : MvPolynomial σ K) (num : I → MvPolynomial σ K)
    {d e : ℕ} (hd : den.totalDegree ≤ d) (hn : ∀ i, (num i).totalDegree ≤ d)
    (p : MvPolynomial I K) (hp : p.totalDegree ≤ e) :
    (clearedSubstitution den num e p).totalDegree ≤ e*d := by
  classical
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_mul ..).trans
  have hnum : (a.prod fun i j => num i ^ j).totalDegree ≤ a.degree * d := calc
    _ ≤ ∑ i ∈ a.support, (num i ^ a i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ a.support, a i * d := Finset.sum_le_sum fun i _ =>
      (totalDegree_pow ..).trans (Nat.mul_le_mul_left _ (hn i))
    _ = a.degree * d := (Finset.sum_mul ..).symm
  have hden := (totalDegree_pow den (e-a.degree)).trans (Nat.mul_le_mul_left _ hd)
  have hm := (totalDegree_mul (C (p.coeff a)) _).trans (by simpa using hnum)
  have he : a.degree ≤ e := (le_totalDegree ha).trans hp
  exact (Nat.add_le_add hm hden).trans_eq (by rw [← Nat.add_mul, Nat.add_sub_of_le he])

/-- The cleared numerator evaluates to the original expression multiplied by the
specified denominator power. This identity needs no division. -/
theorem eval_clearedSubstitution {L : Type*} [CommRing L] [Algebra K L]
    (x : σ → L) (g : I → L) (den : MvPolynomial σ K) (num : I → MvPolynomial σ K)
    (hg : ∀ i, g i * aeval x den = aeval x (num i)) {e : ℕ}
    (p : MvPolynomial I K) (hp : p.totalDegree ≤ e) :
    aeval x (clearedSubstitution den num e p) = aeval g p * (aeval x den)^e := by
  classical
  conv_rhs => lhs; rw [p.as_sum, map_sum]
  simp only [clearedSubstitution, map_sum, map_mul, map_pow, aeval_C, aeval_monomial, Finsupp.prod,
    map_prod, ← hg, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  change _ * (_ * (aeval x den)^a.degree) * (aeval x den)^(e-a.degree) = _ * _ * (aeval x den)^e
  have he : a.degree ≤ e := (le_totalDegree ha).trans hp
  rw [mul_assoc, mul_assoc, ← pow_add, Nat.add_sub_of_le he, mul_assoc]

/-- If a chart function vanishes, the corresponding target value lies on one nonzero
hypersurface of bounded degree. This holds on every point of the graph, since the identity
obtained over its generic parameter field belongs to the graph's defining kernel. -/
theorem rational_chart_bad_locus {L : Type*} [Infinite K] [Field L] [Algebra K L] {m d e : ℕ}
    (x : Fin m → L) (g : I → L) (den : MvPolynomial (Fin m) K) (num : I → MvPolynomial (Fin m) K)
    (hden : aeval x den ≠ 0) (hd : den.totalDegree ≤ d) (hn : ∀ i, (num i).totalDegree ≤ d)
    (hg : ∀ i, g i * aeval x den = aeval x (num i))
    (δ : MvPolynomial I K) (ψ : Fin m → MvPolynomial I K) (hδ : aeval g δ ≠ 0)
    (hδd : δ.totalDegree ≤ e) (hψd : ∀ i, (ψ i).totalDegree ≤ e) :
    ∃ f : MvPolynomial (Fin m) K, f ≠ 0 ∧ f.totalDegree ≤ perronSimplexBound (m+1) (e*d+1) ∧
      ∃ q : MvPolynomial I K, aeval g (aeval ψ f - δ*q) = 0 := by
  let v : Fin (m+1) → MvPolynomial I K := Fin.cons δ ψ
  let N := fun i => clearedSubstitution den num e (v i)
  have hv (i) : (v i).totalDegree ≤ e := Fin.cases hδd hψd i
  have hn' (i) : (N i).totalDegree ≤ e*d := clearedSubstitution_degree den num hd hn _ (hv i)
  have hnD : (den^e).totalDegree ≤ e*d := (totalDegree_pow ..).trans (Nat.mul_le_mul_left _ hd)
  let p := fun i => aeval g (ψ i)
  have hfrac (i : Fin (m+1)) :
      (Fin.cons (aeval g δ) p : Fin (m+1) → L) i * aeval x (den^e) = aeval x (N i) := by
    rw [map_pow, eval_clearedSubstitution x g den num hg _ (hv i)]
    congr 1
    exact Fin.cases rfl (fun _ => rfl) i
  obtain ⟨f, hf, hfd, q, hq⟩ := rational_bad_locus x p (aeval g δ) hδ (den^e) N
    (by rw [map_pow]; exact pow_ne_zero _ hden) hnD hn' hfrac
  refine ⟨f, hf, hfd, aeval v q, ?_⟩
  rw [map_sub, map_mul, sub_eq_zero, ← AlgHom.comp_apply (aeval g) (aeval ψ),
    ← AlgHom.comp_apply (aeval g) (aeval v), comp_aeval, comp_aeval]
  have he : (fun i => aeval g (v i)) = Fin.cons (aeval g δ) p := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he]
  exact hq

end Branch

end BorderVNP
end Computability
end OAI
