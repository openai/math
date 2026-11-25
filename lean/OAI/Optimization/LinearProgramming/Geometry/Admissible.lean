import OAI.Optimization.LinearProgramming.Geometry.Clipping
import OAI.Optimization.LinearProgramming.Geometry.LabelBasis
import OAI.Optimization.LinearProgramming.Geometry.FrameControl

/-! Use a single four-term minor assignment to control the three kinds of
inner product entering the label decision. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule
open scoped BigOperators Matrix

variable {κ : Type*} {n r s : ℕ}

/-- A normalized priced row is tagged by its original row-space vector and the
indices of all its nonzero minors.  The scalar outside the normalization allows
the pivot's orientation sign. -/
def RegisteredVector (W : Submodule ℝ (Fin n → ℝ)) (ell f : κ → ℝ)
    (price x : Fin n → ℝ) : Prop :=
  ∃ (raw logs : Fin n → ℝ) (orientation : ℝ), raw ∈ W ∧ |orientation| ≤ 1 ∧
    (∀ i, raw i ≠ 0 → ∃ u, f u = logs i ∧ ell u = Real.logb 2 |raw i|) ∧
    x = fun j => orientation * normalizedMinorRow raw logs price j

/-- The four-term guarantee is required on one global extension, for the exact
minor indices common to every row in both systems. -/
def FourLogAccuracy [Fintype κ] (B : ℝ) (ell f : κ → ℝ) : Prop :=
  ∀ z : κ → ℤ, (∑ u, |(z u : ℝ)|) ≤ 4 →
    |Compression.clip B (Compression.intForm z f) -
       Compression.clip B (Compression.intForm z ell)| ≤ (2 : ℝ) ^ (-B)

theorem RegisteredVector.abs_le_one {W : Submodule ℝ (Fin n → ℝ)} {ell f : κ → ℝ}
    {price x : Fin n → ℝ} (h : RegisteredVector W ell f price x) (i : Fin n) : |x i| ≤ 1 := by
  obtain ⟨a, g, σ, _, hσ, _, rfl⟩ := h
  rw [abs_mul]
  exact (mul_le_mul hσ (abs_normalizedMinorRow_le_one ..) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem registered_dot_bound [Fintype κ] {W V : Submodule ℝ (Fin n → ℝ)} {ell f : κ → ℝ}
    {t x y : Fin n → ℝ} (horth : ∀ a ∈ W, ∀ b ∈ V, a ⬝ᵥ b = 0)
    (hx : RegisteredVector W ell f t x) (hy : RegisteredVector V ell f (-t) y)
    (B : ℝ) (hB : 2 ≤ B) (hc : FourLogAccuracy B ell f) :
    |x ⬝ᵥ y| ≤ 8 * n * (2 : ℝ) ^ (-B) := by
  obtain ⟨a, g, u, ha, hu, hgu, rfl⟩ := hx
  obtain ⟨b, h, v, hb, hv, hhv, rfl⟩ := hy
  have hclose := almostOrthogonal_normalizedMinorRows a b g h t B hB (horth _ ha _ hb) (by
    intro i j hi hj
    obtain ⟨ai, hfi, hei⟩ := hgu i (mul_ne_zero_iff.mp hi).1
    obtain ⟨bi, hgi, hdi⟩ := hhv i (mul_ne_zero_iff.mp hi).2
    obtain ⟨aj, hfj, hej⟩ := hgu j (mul_ne_zero_iff.mp hj).1
    obtain ⟨bj, hgj, hdj⟩ := hhv j (mul_ne_zero_iff.mp hj).2
    simpa only [hfi, hgi, hfj, hgj, hei, hdi, hej, hdj] using
      fourTermClip_of_intForm ell f B _ hc ai bi aj bj)
  rw [Fintype.card_fin] at hclose
  have hfac : |u*v| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hu hv (abs_nonneg v) zero_le_one).trans_eq (one_mul _)
  have hsum :
      ((fun j => u * normalizedMinorRow a g t j) ⬝ᵥ (fun j => v * normalizedMinorRow b h (-t) j)) =
      (u*v) * (∑ i, normalizedMinorRow a g t i * normalizedMinorRow b h (-t) i) := by
    unfold dotProduct
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, abs_mul]
  exact (mul_le_mul_of_nonneg_right hfac (abs_nonneg _)).trans (by simpa using hclose)

/-- The rounded approximation used by the program keeps signs and pivots in its
row table; all it needs for the correlation estimate is this coordinatewise error. -/
def RoundedRegistered (W : Submodule ℝ (Fin n → ℝ)) (ell f : κ → ℝ)
    (price : Fin n → ℝ) (δ : ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ u, RegisteredVector W ell f price u ∧ ∀ i, |x i - u i| ≤ δ

theorem RegisteredVector.rounded {W : Submodule ℝ (Fin n → ℝ)} {ell f : κ → ℝ}
    {t x : Fin n → ℝ} (h : RegisteredVector W ell f t x) {δ : ℝ} (hδ : 0 ≤ δ) :
    RoundedRegistered W ell f t δ x := ⟨x, h, fun _ => by simpa using hδ⟩

/-- This includes single-row rounding by setting one error to zero. -/
theorem roundedRegistered_dot_bound [Fintype κ] {W V : Submodule ℝ (Fin n → ℝ)} {ell f : κ → ℝ}
    {t x y : Fin n → ℝ} (horth : ∀ a ∈ W, ∀ b ∈ V, a ⬝ᵥ b = 0)
    (hx₁ : ∀ i, |x i| ≤ 1)
    (hx : RoundedRegistered W ell f t (geoDelta n) x)
    (hy : RoundedRegistered V ell f (-t) (geoDelta n) y)
    (hc : FourLogAccuracy (geoCutoff n : ℝ) ell f) :
    |x ⬝ᵥ y| ≤ 10 * n * geoDelta n := by
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  have hB : (2 : ℝ) ≤ (geoCutoff n : ℝ) := by
    exact_mod_cast (show 2 ≤ geoCutoff n by unfold geoCutoff; nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)])
  have h₁ := registered_dot_bound horth hu hv _ hB hc
  change |u ⬝ᵥ v| ≤ 8*n*geoDelta n at h₁
  have h₂ := dotProduct_rounding_error u v x y (geoDelta n) (geoDelta n) hx₁ hv.abs_le_one hxu hyv
  rw [Fintype.card_fin] at h₂
  change |x ⬝ᵥ y - u ⬝ᵥ v| ≤ (n:ℝ) * (geoDelta n + geoDelta n) at h₂
  calc
    |x ⬝ᵥ y| = |(x ⬝ᵥ y - u ⬝ᵥ v) + u ⬝ᵥ v| := by rw [sub_add_cancel]
    _ ≤ |x ⬝ᵥ y - u ⬝ᵥ v| + |u ⬝ᵥ v| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- The label depends only on the rounded primal row matrix. A single four-term
assignment for the genuine rows provides all comparison data on both sides. -/
theorem label_of_registered_frames [Fintype κ] {W V : Submodule ℝ (Fin n → ℝ)}
    (ell f : κ → ℝ) (hc : FourLogAccuracy (geoCutoff n) ell f)
    (horth : ∀ a ∈ W, ∀ b ∈ V, a ⬝ᵥ b = 0)
    (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (d : Fin r → Fin n) (e : Fin s → Fin n)
    (hD : IsPivotFrame (D.map (Rat.castHom ℝ)) d) (hE : IsPivotFrame (E.map (Rat.castHom ℝ)) e)
    (hrank : r + s = n) (t : Fin n → ℝ)
    (hd : ∀ j, RoundedRegistered W ell f t (geoDelta n) ((D.map (Rat.castHom ℝ)).row j))
    (he : ∀ j, RoundedRegistered V ell f (-t) (geoDelta n) ((E.map (Rat.castHom ℝ)).row j))
    (C C' : Finset (Fin n → ℝ)) (hC : ∀ c ∈ C, ∀ j, 0 ≤ c j) (hC' : ∀ c ∈ C', ∀ j, 0 ≤ c j)
    (hcx : ∀ c ∈ C, RegisteredVector W ell f t (priceNormalize t c))
    (hcy : ∀ c ∈ C', RegisteredVector V ell f (-t) (priceNormalize (-t) c))
    (i : Fin n) :
    let answer := fwLabel (1 - rowGramProjector D) i
    ((0 < circuitEnvelope C i ∧ ∀ j, 0 < circuitEnvelope C j →
      circuitCost C i + t i ≤ circuitCost C j + t j + 2) → answer = true) ∧
    ((0 < circuitEnvelope C' i ∧ ∀ j, 0 < circuitEnvelope C' j →
      circuitCost C' i - t i ≤ circuitCost C' j - t j + 2) → answer = false) := by
  apply label_from_rounded_row_bounds D (E.map (Rat.castHom ℝ)) hD.independent hE.independent
      hrank t C C' hC hC'
  · intro j k
    exact roundedRegistered_dot_bound horth (hD.bounded j) (hd j) (he k) hc
  · intro c h k
    rw [dotProduct_comm]
    exact roundedRegistered_dot_bound horth (abs_priceNormalize_le_one _ _)
      ((hcx c h).rounded (geoDelta_nonneg n)) (he k) hc
  · intro c h j
    exact roundedRegistered_dot_bound horth (hD.bounded j) (hd j)
      ((hcy c h).rounded (geoDelta_nonneg n)) hc
  · exact hD.coeff_bound i (by omega)
  · exact hE.coeff_bound i (by omega)

end Geometry
end LinearProgramming
end Optimization
end OAI
