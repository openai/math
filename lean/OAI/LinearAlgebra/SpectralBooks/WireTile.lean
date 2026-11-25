import OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison

namespace OAI
/-! # Finite-list tensor comparison with a sublinear selector cost -/

open scoped BigOperators NNReal Classical

noncomputable section

namespace LinearAlgebra.SpectralBooks.SiteTensor

universe v

variable {I K J : Type*} [Fintype I] [Nonempty I] [Field K] [Fintype J] [Nonempty J]

/-- When every spectral point prices one supply at least as highly as the demand, arbitrarily
large powers of the demand admit an ordinary sum decomposition. Each summand is a local
restriction of a product of supplies with total multiplicity exactly the power. The integer
`s` counts selector bits for the entire decomposition. -/
theorem exists_finite_packet (X : TensorClass.{v} I K) (Y : J → TensorClass.{v} I K)
    (hX : X ≠ 0) (hY : ∀ j, Y j ≠ 0)
    (cover : ∀ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop),
      ∃ j, f.val X ≤ f.val (Y j)) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    ∃ b s : ℕ, N < b ∧ (s : ℝ) ≤ η * b ∧
      ∀ R : Raw.{v} I K, ofRaw R = X ^ b →
        ∃ L : ℕ, L ≤ 2 ^ s ∧ ∃ z : Fin L → (∀ i, R.Leg i) → K,
          R.coeff = ∑ l, z l ∧ ∀ l, ∃ n : J → ℕ, ∑ j, n j = b ∧
            ofRaw { R with coeff := z l } ≤ ∏ j, Y j ^ n j := by
  classical
  let A := Bool × J
  let q := Fintype.card A
  obtain ⟨k, hk⟩ := exists_nat_gt (((1 + q : ℕ) : ℝ) / η)
  have hk' : ((1 + q : ℕ) : ℝ) < η * k := by
    simpa [mul_comm] using (div_lt_iff₀ hη).mp hk
  have hkpos : 0 < k := by
    exact_mod_cast (div_pos (by positivity : 0 < ((1 + q : ℕ) : ℝ)) hη).trans hk
  let supply (p : A) := Y p.2 ^ k
  have gap (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
      f.val (X ^ k) < f.val (∑ p, supply p) := by
    let φ := normalizedSpectrum.toRingHom f
    obtain ⟨j, hj⟩ := cover f
    change φ (X ^ k) < φ (∑ p, supply p)
    rw [map_pow, map_sum]
    have he : φ (X) ^ k ≤ φ (supply (false, j)) := by
      change φ X ≤ φ (Y j) at hj
      simpa [supply] using pow_le_pow_left' hj k
    have hp : 0 < φ (supply (true, j)) := by
      have hy : 0 < φ (Y j) := spectral_value_pos f (hY j)
      simpa [supply] using pow_pos hy k
    have pair_le : φ (supply (false, j)) + φ (supply (true, j)) ≤ ∑ p, φ (supply p) := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun p => φ (supply p)) (Finset.subset_univ ({(false, j), (true, j)} : Finset A))
        (fun _ _ _ => bot_le)
      simpa [A] using h
    exact he.trans_lt ((lt_add_of_pos_right _ hp).trans_le pair_le)
  have nz : ∑ p, supply p ≠ 0 := by
    intro h
    let j : J := Classical.arbitrary J
    let p : A := (false, j)
    apply pow_ne_zero k (hY j)
    change supply p = 0
    apply le_antisymm _ (zero_le_tensor _)
    rw [← h, ← Finset.sum_erase_add Finset.univ supply (Finset.mem_univ p)]
    simpa only [zero_add] using add_mono (zero_le_tensor _) (le_refl (supply p))
  obtain ⟨C, hC, compare⟩ := strictSpectralComparison I K (X^k) (∑ p, supply p)
    (pow_ne_zero _ hX) nz gap
  let h := max C (N + 1)
  have hCh : C ≤ h := le_max_left _ _
  have hNh : N < h := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let P := Fin C × (Fin h → A)
  let source (p : P) := ∏ t, supply (p.2 t)
  have expand : C • ((∑ p, supply p) ^ h) = ∑ p, source p := by
    change _ = ∑ p : Fin C × (Fin h → A), ∏ t, supply (p.2 t)
    conv_rhs => rw [Fintype.sum_prod_type]
    have hex : (∑ p, supply p) ^ h = ∑ w : Fin h → A, ∏ t, supply (w t) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Fintype.prod_sum (fun (_ : Fin h) (a : A) => supply a)
    rw [hex]
    simp
  refine ⟨k * h, (1 + q) * h, hNh.trans_le (Nat.le_mul_of_pos_left _ hkpos), ?_, ?_⟩
  · push_cast
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk'.le) (Nat.cast_nonneg h)
  intro R hR
  obtain ⟨z, hz, hrestr⟩ := images_of_le_sum R source (by
    rw [hR, ← expand, pow_mul]
    exact compare h (hC.trans_le hCh))
  let e := Fintype.equivFin P
  have hcard : Fintype.card P ≤ 2 ^ ((1 + q) * h) := by
    change Fintype.card (Fin C × (Fin h → A)) ≤ _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    change C * q ^ h ≤ _
    rw [Nat.add_mul, one_mul, pow_add, pow_mul]
    exact Nat.mul_le_mul (hCh.trans (Nat.lt_two_pow_self (n := h)).le)
      (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := q)).le h)
  refine ⟨Fintype.card P, hcard, z ∘ e.symm, hz.trans (Fintype.sum_equiv e _ _ (by simp)), ?_⟩
  intro l
  let w (t : Fin h) := ((e.symm l).2 t).2
  let fiber (j : J) := (Finset.univ : Finset (Fin h)).filter (fun t => w t = j)
  refine ⟨fun j => k * (fiber j).card, ?_, (hrestr (e.symm l)).trans_eq ?_⟩
  · rw [← Finset.mul_sum]
    congr 1
    simpa [fiber] using Finset.sum_fiberwise' (s := (Finset.univ : Finset (Fin h))) w (fun _ => (1 : ℕ))
  · change (∏ t, Y (w t) ^ k) = ∏ j, Y j ^ (k * (fiber j).card)
    symm
    simpa [fiber, pow_mul] using (Finset.prod_fiberwise' (Finset.univ : Finset (Fin h)) w
      (fun j => Y j ^ k))

end LinearAlgebra.SpectralBooks.SiteTensor

end
end OAI
