import OAI.Computability.BorderVNP.BranchAffineTarget
import OAI.Computability.BorderVNP.BranchCurveGraphCoordinates

/-! # The selected affine slice rows on the graph deformation

Clear each degree-one graph slice in the original parameters, evaluate the chosen
target on the generic component, and obtain the actual roots and nonzero Jacobian
in those parameters. The fiber and the affine equations use the same slice polynomials.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {I K T L : Type*} [Field K] [Field T] [Field L] [Algebra K T] [Algebra K L]
  [Algebra T L] [IsScalarTower K T L] {m d : ℕ}

/-- Graph-coordinate numerators in the original affine parameters. -/
noncomputable def affineGraphNums (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m)) :
    Option (Fin m) ⊕ I → MvPolynomial (Fin m) K :=
  Sum.elim affineChartDen (fun i => Y i * affineChartDen k)

/-- Numerator of a degree-one graph slice expressed in the original affine parameters. -/
noncomputable def affineSlice (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (row : MvPolynomial (Option (Fin m) ⊕ I) K) : MvPolynomial (Fin m) K :=
  clearedSubstitution (affineChartDen k) (affineGraphNums Y k) 1 row

/-- A linear graph slice gives an affine numerator of degree at most `d + 1`. -/
theorem affineSlice_degree (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (row : MvPolynomial (Option (Fin m) ⊕ I) K) (hY : ∀ i, (Y i).totalDegree ≤ d)
    (hr : row.totalDegree ≤ 1) : (affineSlice Y k row).totalDegree ≤ d+1 := by
  have hd := (affineChart_degrees (K := K) k).1
  have hn (j) : (affineGraphNums Y k j).totalDegree ≤ d+1 := by
    cases j with
    | inl l => exact (affineChart_degrees (K := K) l).1.trans (by omega)
    | inr i => exact (totalDegree_mul ..).trans (Nat.add_le_add (hY i) hd)
  simpa only [affineSlice, one_mul] using clearedSubstitution_degree (affineChartDen k)
    (affineGraphNums Y k) (hd.trans (by omega)) hn row hr

/-- The graph map whose fiber at `v` is the deformation (9.1) at generic `t`. -/
noncomputable def displacementMap (k : Option (Fin m)) (t : T)
    (D : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K) (i : Fin m) :
    MvPolynomial (Option (Fin m) ⊕ I) T :=
  X (.inl (chartIndex k i)) + C t⁻¹ * map (algebraMap K T) (D i)

private theorem mapDegree (p : MvPolynomial I K) :
    (map (algebraMap K T) p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective _ (algebraMap K T).injective]

/-- Select the finite advice-field target for the specified degree-one graph rows. -/
theorem choose_affine_slice_target (E₀ : Type*) [Field E₀] [Fintype E₀] [Algebra E₀ K] [IsAlgClosed K]
    [Infinite T] [Algebra (Polynomial K) T] [IsScalarTower K (Polynomial K) T]
    [IsFractionRing (Polynomial K) T] (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (hY : ∀ i, (Y i).totalDegree ≤ d) (D : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K)
    (hD : ∀ i, (D i).totalDegree ≤ 1) :
    let t := algebraMap (Polynomial K) T Polynomial.X
    let A := fun i => map (algebraMap K T) (affineSlice Y k (D i))
    let s := m*(2*(d+1))
    ∃ E : IntermediateField E₀ K, Finite E ∧ Nat.card E ≤ Fintype.card E₀ * max (displacementDegree m d (d+1)) 1 ∧
      ∃ (v : Fin m → E) (f : MvPolynomial (Fin m) T), eval (fun i => algebraMap K T (v i : K)) f ≠ 0 ∧
        ∃ q : MvPolynomial (Option (Fin m) ⊕ I) T,
          graphChartMap (fun i => map (algebraMap K T) (Y i)) k
            (aeval (displacementMap k t D) f - affineChartException k t A s * q) = 0 := by
  let t := algebraMap (Polynomial K) T Polynomial.X
  have hψ (i) : (displacementMap k t D i).totalDegree ≤ 1 := by
    apply (totalDegree_add ..).trans (max_le (by simp) _)
    exact (totalDegree_mul ..).trans (by simpa only [totalDegree_C, zero_add, mapDegree] using hD i)
  exact exists_good_affine_target E₀ (fun i => map (algebraMap K T) (Y i)) k
    (fun i => (mapDegree (T := T) _).trans_le (hY i)) (fun i => affineSlice Y k (D i))
    (by omega) (fun i => affineSlice_degree Y k _ hY (hD i)) (displacementMap k t D) hψ

private theorem aeval_map_tower {σ : Type*} (x : σ → L) (p : MvPolynomial σ K) :
    aeval x (map (algebraMap K T) p) = aeval x p := by
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K T L]
  rfl

private theorem root_finite_chart (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (φ : ChartRing Y k →ₐ[K] L) (hk : homogeneousParameters (Fin m) K k ≠ 0)
    (hd : φ (chartRatio Y k none) ≠ 0) :
    let z := Sum.elim (fun j => φ (chartRatio Y k j)) (fun i => φ (chartOutput Y k i))
    let x := chartParameters Y k φ
    ∀ j, z j * aeval x (affineChartDen (K := K) k) = aeval x (affineGraphNums Y k j) := by
  intro z x
  have hgen : chartRatio Y k k = 1 := by
    apply Subtype.ext
    change aeval (graphValues Y k) (X (.inl k)) = 1
    rw [aeval_X]; exact div_self hk
  have hkey : z (.inl k) = 1 := by change φ (chartRatio Y k k) = 1; rw [hgen, map_one]
  have hx (i) : z (.inl (some i)) / z (.inl none) = x i := rfl
  have hden : aeval x (affineChartDen (K := K) k) = (z (.inl none))⁻¹ := by
    cases k with
    | none => simp [affineChartDen, hkey]
    | some j => rw [affineChartDen, Option.elim_some, aeval_X, ← hx, hkey, one_div]
  intro j
  cases j with
  | inl j =>
    rw [hden]
    cases j with
    | none => exact (mul_inv_cancel₀ hd).trans (map_one _).symm
    | some j => simpa only [affineGraphNums, Sum.elim_inl, affineChartDen, Option.elim_some,
        aeval_X, ← div_eq_mul_inv] using hx j
  | inr i =>
    change φ (chartOutput Y k i) * _ = aeval x (Y i * affineChartDen k)
    rw [map_mul, chartOutput_specializes Y k φ hd i]

/-- At every generic component root of the graph deformation the affine row equations
vanish and their actual Jacobian is invertible. -/
theorem affine_slice_component_root [Infinite K] (Y : I → MvPolynomial (Fin m) K)
    (k : Option (Fin m)) (hk : homogeneousParameters (Fin m) K k ≠ 0)
    (D : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K) (hD : ∀ i, (D i).totalDegree ≤ 1)
    (hY : ∀ i, (Y i).totalDegree ≤ d) (t : T) (ht : t ≠ 0)
    (v : Fin m → T) (f : MvPolynomial (Fin m) T) (hv : eval v f ≠ 0)
    (q : MvPolynomial (Option (Fin m) ⊕ I) T)
    (he : graphChartMap (fun i => map (algebraMap K T) (Y i)) k
      (aeval (displacementMap k t D) f -
        affineChartException k t (fun i => map (algebraMap K T) (affineSlice Y k (D i))) (m*(2*(d+1))) * q) = 0)
    (φ : ChartRing Y k →ₐ[K] L)
    (hroot : ∀ i, φ ((graphChartAlgHom Y k).rangeRestrict (D i)) +
      algebraMap T L t * (φ (chartRatio Y k (chartIndex k i)) - algebraMap T L (v i)) = 0) :
    φ (chartRatio Y k none) ≠ 0 ∧
      let x := chartParameters Y k φ
      let A := fun i => map (algebraMap K T) (affineSlice Y k (D i))
      (∀ i, aeval x (affineRow k t A v i) = 0) ∧
      (Matrix.of fun i j => aeval x (pderiv j (affineRow k t A v i))).det ≠ 0 := by
  let z := Sum.elim (fun j => φ (chartRatio Y k j)) (fun i => φ (chartOutput Y k i))
  let x := chartParameters Y k φ
  let A (i) := map (algebraMap K T) (affineSlice Y k (D i))
  have hmap : aeval (R := K) z = φ.comp (graphChartAlgHom Y k).rangeRestrict := by
    ext j
    rw [aeval_X, AlgHom.comp_apply]
    cases j <;> rfl
  have hz : RingHom.ker (graphChartMap Y k) ≤ RingHom.ker (aeval (R := K) z).toRingHom := by
    intro p hp
    change aeval z p = 0
    rw [hmap, AlgHom.comp_apply]
    have h : (graphChartAlgHom Y k).rangeRestrict p = 0 := by
      apply Subtype.ext
      change (graphChartAlgHom Y k).toRingHom p = 0
      rwa [graphChartAlgHom_toRingHom]
    rw [h, map_zero]
  have hr (i) : aeval z (D i) + algebraMap T L t * (z (.inl (chartIndex k i)) - algebraMap T L (v i)) = 0 := by
    rw [hmap, AlgHom.comp_apply]
    exact hroot i
  have hψ (i) : aeval z (displacementMap k t D i) = algebraMap T L (v i) := by
    simp only [displacementMap, map_add, map_mul, aeval_X, aeval_C, map_inv₀, aeval_map_tower]
    have hn := (map_ne_zero_iff (algebraMap T L) (algebraMap T L).injective).mpr ht
    field_simp [hn]
    linear_combination hr i
  have hJ := affineDisplacementJacobian_degree k t A (d := d+1) (by omega)
    (fun i => (mapDegree (T := T) _).trans_le (affineSlice_degree Y k _ hY (hD i)))
  obtain ⟨hd, hreg⟩ := good_affine_target_nonsingular Y k t A _ hJ _ f q he z hz v hv hψ
  have hchart := root_finite_chart Y k φ hk hd
  have ha (i) : aeval x (affineSlice Y k (D i)) = aeval z (D i) * aeval x (affineChartDen (K := K) k) := by
    rw [affineSlice, eval_clearedSubstitution x z _ _ hchart _ (hD i), pow_one]
  have hu (i) : z (.inl (chartIndex k i)) * aeval x (affineChartDen (K := K) k) =
      aeval x (affineChartDen (K := K) (chartIndex k i)) := hchart (.inl (chartIndex k i))
  have hconstant (j) : aeval (R := T) x (affineChartDen j) = aeval (R := K) x (affineChartDen j) := by
    cases j <;> simp [affineChartDen]
  have roots (i) : aeval x (affineRow k t A v i) = 0 := by
    simp only [affineRow, map_sub, map_add, map_mul, aeval_C, A, aeval_map_tower, ha, hconstant]
    change _ + _ * aeval (R := T) x (affineChartDen (chartIndex k i)) - _ = 0
    rw [hconstant, ← hu]
    linear_combination aeval x (affineChartDen (K := K) k) * hr i
  exact ⟨hd, roots, hreg roots⟩

end Branch

end BorderVNP
end Computability
end OAI
