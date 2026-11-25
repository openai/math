import OAI.LinearAlgebra.FiniteFourier.ProtectedShears

/-! # Unit pivots over a semilocal ring

Simultaneous lifting from the residue fields gives a unit pivot in any unimodular
column. If the residue fields have a common third element distinct from zero and
one, every shear coefficient splits as a sum of two units.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R]

private theorem lift_maximal_residues [Finite (MaximalSpectrum R)]
    (r : (m : MaximalSpectrum R) → R ⧸ m.asIdeal) :
    ∃ t : R, ∀ m, Ideal.Quotient.mk m.asIdeal t = r m :=
  Ideal.pi_quotient_surjective
    (fun _ _ h => Ideal.isCoprime_of_isMaximal (fun e => h (MaximalSpectrum.ext e))) r

private theorem unit_of_nonzero_maximal_residues (x : R)
    (hx : ∀ m : MaximalSpectrum R, Ideal.Quotient.mk m.asIdeal x ≠ 0) : IsUnit x := by
  by_contra h
  obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits h
  exact hx ⟨I, hI⟩ (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)

/-- Either `1` or `b` can be used for the first summand in each residue field. -/
theorem exists_unit_split_of_third_residue [Finite (MaximalSpectrum R)] {b : R}
    (hb : IsUnit b) (hb1 : IsUnit (b-1)) (μ : R) :
    ∃ t : R, IsUnit t ∧ IsUnit (μ-t) := by
  classical
  let π (m : MaximalSpectrum R) := Ideal.Quotient.mk m.asIdeal
  let r (m : MaximalSpectrum R) : R ⧸ m.asIdeal := if π m μ = 1 then π m b else 1
  obtain ⟨t, ht⟩ := lift_maximal_residues r
  refine ⟨t, unit_of_nonzero_maximal_residues t (fun m => ?_),
    unit_of_nonzero_maximal_residues _ (fun m => ?_)⟩
  · rw [ht m]
    by_cases h : π m μ = 1 <;> simp [r, h, (hb.map (π m)).ne_zero]
  · change π m (μ - t) ≠ 0
    rw [map_sub, show π m t = r m from ht m]
    by_cases h : π m μ = 1
    · have hne : π m b ≠ 1 := by simpa [sub_ne_zero] using (hb1.map (π m)).ne_zero
      simp [r, h, sub_ne_zero, Ne.symm hne]
    · simp [r, h, sub_ne_zero]

/-- A unimodular column can be pivoted by adding multiples of its lower entries
to its first entry. In residue fields where the first entry vanishes, use the
Bézout row to obtain one. In the other residue fields, use zero multiples. -/
theorem exists_semilocal_unit_pivot [Finite (MaximalSpectrum R)] {n : ℕ}
    (x a : Fin (n+1) → R) (ha : ∑ i, a i * x i = 1) :
    ∃ c : Fin n → R, IsUnit (x 0 + ∑ i, c i * x i.succ) := by
  classical
  let π (m : MaximalSpectrum R) := Ideal.Quotient.mk m.asIdeal
  obtain ⟨d, hd⟩ := lift_maximal_residues (R := R) fun m =>
    if π m (x 0) = 0 then 1 else 0
  refine ⟨fun i => d * a i.succ, unit_of_nonzero_maximal_residues _ (fun m => ?_)⟩
  change π m (x 0 + ∑ i : Fin n, d * a i.succ * x i.succ) ≠ 0
  have hm : π m d = if π m (x 0) = 0 then 1 else 0 := hd m
  simp_rw [mul_assoc, ← Finset.mul_sum, map_add, map_mul, hm]
  by_cases h : π m (x 0) = 0
  · rw [Fin.sum_univ_succ] at ha
    have he := congrArg (π m) ha
    simp only [map_add, map_mul, h, mul_zero, zero_add, map_one] at he
    simp [h, he]
  · simp [h]

/-- A primitive ninth root supplies a common third element whenever nine is
invertible, including over a domain with residue characteristic two. -/
theorem exists_unit_split_of_ninth_root [Finite (MaximalSpectrum R)] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 9) (hn : IsUnit (9 : R)) (μ : R) :
    ∃ t : R, IsUnit t ∧ IsUnit (μ-t) := by
  have hsub : IsUnit (ζ - 1) := by
    simpa only [pow_one, neg_sub] using
      (newtonFactor_isUnit hζ hn (j := 1) (by decide) (by decide)).neg
  exact exists_unit_split_of_third_residue (hζ.isUnit (by decide)) hsub μ

end FiniteFourier
end LinearAlgebra
end OAI
