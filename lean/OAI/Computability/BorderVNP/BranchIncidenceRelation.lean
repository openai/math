import OAI.Computability.BorderVNP.BranchIncidenceCount
import OAI.Computability.BorderVNP.BranchIncidenceProducts
import OAI.Computability.BorderVNP.BranchRationalSubstitution

/-!
# Bounded relations on the incidence strata of the weighted slices

On the stratum where the slice polynomial has leading coefficient `G ≠ 0`,
the `h` slice scalars are roots of a fixed polynomial in one variable.
Reducing powers of each root independently and applying a monomial count to
the rational parametrization of the graph gives a bounded equation relating
the roots to any one graph coordinate. The equation remains valid at graph
points where the original chart denominator vanishes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch.Incidence

open MvPolynomial

variable {I K L : Type*} [Field K] [Field L] [Algebra K L] {h r d : ℕ}

private noncomputable def boxDegree {m k : ℕ} (u : Fin m → Fin (k+1)) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (u i).val

private theorem boxDegree_injective {m k : ℕ} : Function.Injective (boxDegree (m := m) (k := k)) := by
  intro u v e
  exact funext fun i => Fin.ext (DFunLike.congr_fun e i)

/-- A graph coordinate on a root incidence stratum satisfies a nonzero
equation with the selected roots. The cutoff depends on the number of
parameters, the root degree and the chart degree. -/
theorem exists_root_relation (z : Fin h → L) (g : I → L)
    (den : MvPolynomial (Fin h) K) (num : I → MvPolynomial (Fin h) K)
    (hden : aeval z den ≠ 0) (hd : den.totalDegree ≤ d) (hn : ∀ i, (num i).totalDegree ≤ d)
    (hg : ∀ i, g i * aeval z den = aeval z (num i))
    (w G : MvPolynomial I K) (f : Fin (r+1) → MvPolynomial I K)
    (hw : w.totalDegree ≤ 1) (hG : G.totalDegree ≤ 1) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    ∃ W : MvPolynomial (Fin (h+1)) K, W ≠ 0 ∧ W.totalDegree ≤ (h+1)*radius h (r+1) d ∧
      ∀ (v : I → K) (a : Fin h → K),
        (∀ p : MvPolynomial I K, aeval g p = 0 → eval v p = 0) → eval v G ≠ 0 →
        (∀ j, eval v G * (a j)^(r+1) + ∑ i, eval v (f i) * (a j)^i.val = 0) →
        eval (Fin.cons (eval v w) a) W = 0 := by
  classical
  let k := radius h (r+1) d
  let b := (h+1)*k
  let slot (u : Fin (h+1) → Fin (k+1)) (l : Fin h → Fin (r+1)) := monomialSlot w G f u l
  have hslot (u l) : (slot u l).totalDegree ≤ b := degree_monomialSlot w G f hw hG hf u l
  let table u l := clearedSubstitution den num b (slot u l)
  have htable u l : (table u l).totalDegree ≤ b*d := clearedSubstitution_degree den num hd hn _ (hslot u l)
  obtain ⟨c, ⟨u₀, hu₀⟩, hc⟩ := exists_slot_relation h (r+1) d table htable
  let W : MvPolynomial (Fin (h+1)) K := ∑ u, monomial (boxDegree u) (c u)
  have hW : W ≠ 0 := by
    intro hz
    have hc₀ := congrArg (fun p : MvPolynomial (Fin (h+1)) K => p.coeff (boxDegree u₀)) hz
    exact hu₀ (by simpa [W, coeff_sum, coeff_monomial, boxDegree_injective.eq_iff] using hc₀)
  have hWd : W.totalDegree ≤ b := by
    apply totalDegree_finsetSum_le
    intro u _
    apply (totalDegree_monomial_le ..).trans
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Nat.le_of_lt_succ (u i).isLt)
    simpa [boxDegree, b] using hle
  have hgraph (l : Fin h → Fin (r+1)) : aeval g (∑ u, c u • slot u l) = 0 := by
    have h := congrArg (aeval z) (hc l)
    have hmap (u) : aeval z (table u l) = aeval g (slot u l) * (aeval z den)^b :=
      eval_clearedSubstitution z g den num hg _ (hslot u l)
    have he : aeval z (∑ u, c u • table u l) =
        aeval g (∑ u, c u • slot u l) * (aeval z den)^b := by
      simp only [map_sum, map_smul, hmap, Finset.sum_mul, smul_mul_assoc]
    rw [he, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hden)
  refine ⟨W, hW, hWd, ?_⟩
  intro v a hv hunit hroots
  have hzero (l : Fin h → Fin (r+1)) : ∑ u, c u * eval v (slot u l) = 0 := by
    simpa [map_sum, smul_eq_C_mul] using hv _ (hgraph l)
  let point : Fin (h+1) → K := Fin.cons (eval v w) a
  have hWval : eval point W = ∑ u, c u * ∏ j, point j ^ (u j).val := by
    simp only [W, map_sum, eval_monomial]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finsupp.prod_fintype _ _ (fun j => pow_zero (point j))]
    rfl
  have hrow (u : Fin (h+1) → Fin (k+1)) :
      eval v G^(h*k) * (∏ j, point j^(u j).val) =
        ∑ l : Fin h → Fin (r+1), eval v (slot u l) * ∏ i, (a i)^(l i).val := by
    simp only [slot, map_monomialSlot]
    exact (sum_monomialSlot (eval v w) (eval v G) (eval v ∘ f) u a hroots).symm
  apply (mul_eq_zero.mp (show (eval v G)^(h*k) * eval point W = 0 from ?_)).resolve_left (pow_ne_zero _ hunit)
  rw [hWval, Finset.mul_sum]
  calc
    _ = ∑ u, c u * (eval v G^(h*k) * ∏ j, point j^(u j).val) := by
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ l : Fin h → Fin (r+1), (∑ u, c u * eval v (slot u l)) * ∏ i, (a i)^(l i).val := by
      simp only [hrow, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
      exact Finset.sum_comm
    _ = 0 := by simp only [hzero, zero_mul, Finset.sum_const_zero]

end Branch.Incidence

end BorderVNP
end Computability
end OAI
