import OAI.Computability.MultitapeWeakETH.TemplateArithmetic
import OAI.Computability.VPVNP.Diagonal

/-! # Common-denominator accumulation of variable-degree template monomials -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open NumberField VPVNP
open scoped NumberField Classical BigOperators
noncomputable section

variable {I K : Type} [Fintype I] [Field K] [NumberField K] (f : I → K) (d : ℤ)
    (integral : ∀ i, IsIntegral ℤ ((d:K)*f i))

private def factors (e : I → ℕ) : List I :=
  Finset.univ.toList.flatMap fun i => List.replicate (e i) i

private theorem factors_degree (e : I → ℕ) : (factors e).length = ∑ i, e i := by
  simp [factors,List.length_flatMap]

omit [NumberField K] in
private theorem factors_product (e : I → ℕ) :
    ((factors e).map f).prod = Diagonal.labelMonomial f e := by
  simp [factors,Diagonal.labelMonomial,List.flatMap_def,List.prod_flatten,Function.comp_def]

/-- Integer numerator over the common denominator d^M. -/
def scaledTerm (M : ℕ) (e : I → ℕ) : 𝓞 K :=
  d^(M - ∑ i, e i) • ((factors e).map (numerator f d integral)).prod

omit [NumberField K] in
theorem scaled_term_eq (M : ℕ) (e : I → ℕ) (bound : (∑ i, e i) ≤ M) :
    algebraMap (𝓞 K) K (scaledTerm f d integral M e) = (d:K)^M*Diagonal.labelMonomial f e := by
  simp only [scaledTerm,zsmul_eq_mul,map_mul,map_pow,map_intCast,Int.cast_pow,scaled_product,
    factors_degree,factors_product,← mul_assoc,← pow_add,Nat.sub_add_cancel bound]

/-- A fixed base bounds the absolute integral-basis coordinates of every
partial sum with degree at most M, with linear dependence on the term count. -/
theorem sum_coordinates :
    ∃ H : ℕ, 0 < H ∧ ∀ {J : Type} (s : Finset J) (e : J → I → ℕ) (M : ℕ),
      (∀ j ∈ s, (∑ i, e j i) ≤ M) → ∀ l,
      (((RingOfIntegers.basis K).repr (∑ j ∈ s, scaledTerm f d integral M (e j)) l).natAbs) ≤
        s.card * H^(M+1) := by
  obtain ⟨C,pos,coord⟩ := coordinates_bound f d integral
  let H := max C d.natAbs
  refine ⟨H, pos.trans_le (le_max_left ..), ?_⟩
  intro J s e M bound l
  simp only [map_sum,Finsupp.finsetSum_apply]
  refine (Int.natAbs_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j ∈ s, H^(M+1) := by
      apply Finset.sum_le_sum
      intro j hj
      let m := ∑ i, e j i
      have ht := coord (factors (e j)) l
      rw [factors_degree] at ht
      rw [scaledTerm,map_smul,Finsupp.smul_apply,smul_eq_mul,Int.natAbs_mul,Int.natAbs_pow]
      calc
        _ ≤ H^(M-m)*H^(m+1) := Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_right ..) _)
          (ht.trans (Nat.pow_le_pow_left (le_max_left ..) _))
        _ = _ := by rw [← pow_add,← Nat.add_assoc,Nat.sub_add_cancel (bound j hj)]
    _ = _ := by simp

/-- The integer accumulator vanishes precisely when the field sum is zero. -/
theorem sum_eq_zero_iff {J : Type} (s : Finset J) (e : J → I → ℕ) (M : ℕ)
    (hd : d ≠ 0) (bound : ∀ j ∈ s, (∑ i, e j i) ≤ M) :
    (∑ j ∈ s, scaledTerm f d integral M (e j)) = 0 ↔
      (∑ j ∈ s, Diagonal.labelMonomial f (e j)) = 0 := by
  have eq : algebraMap (𝓞 K) K (∑ j ∈ s, scaledTerm f d integral M (e j)) =
      (d:K)^M*(∑ j ∈ s, Diagonal.labelMonomial f (e j)) := by
    rw [map_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => scaled_term_eq f d integral M (e j) (bound j hj)
  have h : (d:K)^M ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr hd)
  rw [← (IsFractionRing.injective (𝓞 K) K).eq_iff, map_zero, eq, mul_eq_zero, or_iff_right h]

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
