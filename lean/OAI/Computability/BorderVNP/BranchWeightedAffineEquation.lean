import OAI.Computability.BorderVNP.BranchAffineDescent
import OAI.Computability.BorderVNP.BranchFiniteCuts

/-! # Reading the actual weighted affine equations

The affine equations produced from the finite graph cut can be evaluated using one
weighted table evaluation, a stored offset, and at most `h + 1` chart coordinates.
The formula is a polynomial identity and remains valid at a zero chart denominator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {I E R : Type*} [Field E] [Field R] [Fintype I] {m : ℕ}

/-- Weighted offset from all prescribed coefficients and pinned parameter coordinates. -/
noncomputable def weightedOffset (c : I → E) (s : Finset (Fin (m+1))) (p : Fin (m+1) → E)
    (e : I → ℕ) (B : ℕ) (a : E) : E :=
  ∑ i, c i * a^e i + ∑ j : s, p j.val * a^(residualExponent e B s (.inr j))

omit [Fintype I] in
private theorem affineSlice_generic (Y : I → MvPolynomial (Fin m) E) (k : Option (Fin m))
    (r : MvPolynomial (Option (Fin m) ⊕ I) E) (hd : r.totalDegree ≤ 1) :
    algebraMap _ (ParameterField (Fin m) E) (affineSlice Y k r) =
      aeval (graphValues Y k) r * algebraMap _ _ (affineChartDen (K := E) k) := by
  let inc := algebraMap (MvPolynomial (Fin m) E) (ParameterField (Fin m) E)
  have hu (j : Option (Fin m)) : inc (affineChartDen j) = homogeneousParameters (Fin m) E j := by
    cases j <;> simp [inc, affineChartDen, homogeneousParameters]
  have hn : inc (affineChartDen k) ≠ 0 := by
    apply (map_ne_zero_iff inc (IsFractionRing.injective _ _)).mpr
    cases k <;> simp [affineChartDen]
  have he (j) : graphValues Y k j * inc (affineChartDen k) = inc (affineGraphNums Y k j) := by
    cases j with
    | inl l =>
      change _ / _ * inc (affineChartDen k) = inc (affineChartDen l)
      rw [← hu, ← hu, div_mul_cancel₀ _ hn]
    | inr i =>
      change inc (eval₂Hom C Y (X i)) * _ = inc (Y i * _)
      rw [eval₂Hom_X', map_mul]
  rw [← eval_affineParameter, affineSlice, eval_clearedSubstitution _ (graphValues Y k) _ _
    (fun i => by simpa only [eval_affineParameter] using he i) _ hd, pow_one, eval_affineParameter]

/-- An equality of formal polynomials gives the compact affine numerator of the actual
weighted graph slice. In particular it holds at all points off and on the chart boundary. -/
theorem affineSlice_weighted (Y : I → MvPolynomial (Fin m) E) (k : Option (Fin m))
    (c : I → E) (s : Finset (Fin (m+1))) (p : Fin (m+1) → E)
    (e : I → ℕ) (B : ℕ) (a : E) :
    affineSlice Y k (graphSliceRow c s p e B a) =
      affineChartDen k * ((∑ i, Y i * C (a^e i)) - C (weightedOffset c s p e B a)) +
      ∑ j : s, affineChartDen ((_root_.finSuccEquiv m) j.val) * C (a^(residualExponent e B s (.inr j))) := by
  classical
  let inc := algebraMap (MvPolynomial (Fin m) E) (ParameterField (Fin m) E)
  let emb := algebraMap E (ParameterField (Fin m) E)
  let den := affineChartDen (K := E) k
  have hconst (u) : inc (C u) = emb u := (IsScalarTower.algebraMap_apply E (MvPolynomial (Fin m) E) _ u).symm
  have ho (i : I) : graphValues Y k (.inr i) = inc (Y i) := by
    change inc (eval₂Hom C Y (X i)) = _
    rw [eval₂Hom_X']
  have hu (j : Option (Fin m)) : inc (affineChartDen j) = homogeneousParameters (Fin m) E j := by
    cases j <;> simp [inc, affineChartDen, homogeneousParameters]
  have hn : inc den ≠ 0 := by
    apply (map_ne_zero_iff inc (IsFractionRing.injective _ _)).mpr
    cases k <;> simp [den, affineChartDen]
  have hp (l : Option (Fin m)) : graphValues Y k (.inl l) * inc den = inc (affineChartDen l) := by
    change _ / _ * inc den = _
    rw [← hu, ← hu, div_mul_cancel₀ _ hn]
  apply IsFractionRing.injective (MvPolynomial (Fin m) E) (ParameterField (Fin m) E)
  change inc _ = inc _
  rw [show inc (affineSlice Y k (graphSliceRow c s p e B a)) =
    aeval (graphValues Y k) (graphSliceRow c s p e B a) * inc den from
      affineSlice_generic Y k _ (graphSliceRow_degree ..)]
  simp only [graphSliceRow, map_sum, map_mul, aeval_C, Fintype.sum_sum_type, fiberResiduals, Sum.elim_inl,
    Sum.elim_inr, map_sub, aeval_X, ho, weightedOffset, hconst, map_add, add_mul, Finset.sum_mul,
    mul_sub, Finset.mul_sum, residualExponent, mul_add]
  have hrow (j : s) (u : ParameterField (Fin m) E) :
      graphValues Y k (.inl ((_root_.finSuccEquiv m) j.val)) * u * inc den =
        inc (affineChartDen ((_root_.finSuccEquiv m) j.val)) * u := by
    rw [mul_right_comm, hp]
  simp only [sub_mul, Finset.sum_sub_distrib, hrow]
  dsimp only [den, emb]
  ring_nf
  have ht (i : I) : inc (Y i) * algebraMap E (ParameterField (Fin m) E) (a^e i) * inc (affineChartDen k) =
      inc (affineChartDen k) * inc (Y i) * algebraMap E (ParameterField (Fin m) E) (a^e i) := by ring
  simp_rw [ht]
  ring

/-- Division-free reader for the exact advice-field equation, including every input
where the chart denominator vanishes. The first sum is the single weighted table
evaluation and the offset is an advice scalar. -/
theorem eval_weighted_affineEquation (f : E →+* R) (Y : I → MvPolynomial (Fin m) E) (k : Option (Fin m))
    (c : I → E) (s : Finset (Fin (m+1))) (p : Fin (m+1) → E)
    (e : I → ℕ) (B : ℕ) (a v : Fin m → E) (i : Fin m) (t : R) (x : Fin m → R) :
    let value := eval₂Hom f x
    let den := value (affineChartDen (K := E) k)
    eval₂Hom f (fun o : Option (Fin m) => o.elim t x)
      (affineEquation Y k (fun j => graphSliceRow c s p e B (a j)) v i) =
      den * ((∑ j, value (Y j) * (f (a i))^(e j)) - f (weightedOffset c s p e B (a i))) +
      (∑ j : s, value (affineChartDen ((_root_.finSuccEquiv m) j.val)) * (f (a i))^(residualExponent e B s (.inr j))) +
      t * (value (affineChartNum k i) - f (v i) * den) := by
  intro value den
  have ev (r : MvPolynomial (Fin m) E) : eval₂Hom f (fun o : Option (Fin m) => o.elim t x)
      (rename some r) = value r := by rw [coe_eval₂Hom, eval₂_rename]; rfl
  simp only [affineEquation, map_add, map_mul, ev, eval₂Hom_X', Option.elim_none, affineSlice_weighted,
    map_sub, map_sum, eval₂Hom_C, map_pow, den, value]

end Branch

end BorderVNP
end Computability
end OAI
