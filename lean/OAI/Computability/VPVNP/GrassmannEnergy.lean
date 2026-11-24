import OAI.Computability.VPVNP.GrassmannSeeds
import OAI.Computability.VPVNP.OrbitAverage
import OAI.Computability.VPVNP.SubspaceOrbits
import OAI.Computability.VPVNP.GrassmannGeometry

/-!
# Averaging the quadrilateral inequality on the binary Grassmannian

The quantities in Lemma 5.3 are uniform means over ordered pairs of a fixed
sum dimension. Transitivity identifies these means with averages of a single
quadrilateral translated by the general linear group. In the saturated case
each translate has zero quadrilateral deficit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

private theorem plane_finrank {m : ℕ} (a : Plane m) : Module.finrank (ZMod 2) a.val = m :=
  a.property

private theorem pair_finrank {m r : ℕ} (p : Pair m r) :
    Module.finrank (ZMod 2) (p.val.1.val ⊔ p.val.2.val : Submodule (ZMod 2) (Space m)) = m + r :=
  p.property

instance (m r : ℕ) : MulAction.IsPretransitive (GL m) (Pair m r) where
  exists_smul_eq p q := by
    obtain ⟨g, hg, hg'⟩ := exists_pair_linearEquiv (K := ZMod 2) (V := Space m) p.val.1.val p.val.2.val
      q.val.1.val q.val.2.val (by rw [plane_finrank, plane_finrank])
      (by rw [plane_finrank, plane_finrank]) (by rw [pair_finrank p, pair_finrank q])
    exact ⟨g, Subtype.ext (Prod.ext (Subtype.ext hg) (Subtype.ext hg'))⟩

variable {m r s : ℕ}

/-- Any seed pair of a given type gives the uniform pair mean under random
linear changes of coordinates. -/
theorem average_translate (D : Plane m → Plane m → ℝ) {a b : Plane m} (h : HasType r a b) :
    (∑ g : GL m, D (g • a) (g • b)) / Fintype.card (GL m) = mean D r :=
  orbitAverage_eq_uniformAverage (GL m) (S := Pair m r) (⟨(a,b), h⟩ : Pair m r)
    (fun p => D p.val.1 p.val.2)

private theorem sum_translate (D : Plane m → Plane m → ℝ) {a b : Plane m} (h : HasType r a b) :
    (∑ g : GL m, D (g • a) (g • b)) = mean D r * Fintype.card (GL m) :=
  (div_eq_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mp (average_translate D h)

/-- The difference between the side and diagonal sums of a quadrilateral. -/
def deficit (D : Plane m → Plane m → ℝ) (a b c d : Plane m) : ℝ :=
  D a b + D b c + D c d + D d a - (D a c + D b d)

/-- Squared CAT(0) distance arrays, and limits of those arrays, obey this inequality. -/
def QuadrilateralBound (D : Plane m → Plane m → ℝ) : Prop :=
  ∀ a b c d, D a c + D b d ≤ D a b + D b c + D c d + D d a

private theorem IsSquare.sum_deficit {a b c d : Plane m} (sq : IsSquare r s a b c d)
    (D : Plane m → Plane m → ℝ) :
    (∑ g : GL m, deficit D (g • a) (g • b) (g • c) (g • d)) =
      2 * (mean D r + mean D s - mean D (r + s)) * Fintype.card (GL m) := by
  simp only [deficit, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_translate D sq.ab, sum_translate D sq.bc, sum_translate D sq.cd, sum_translate D sq.da,
    sum_translate D sq.ac, sum_translate D sq.bd]
  ring

theorem IsSquare.mean_add_le {a b c d : Plane m} (sq : IsSquare r s a b c d)
    {D : Plane m → Plane m → ℝ} (h : QuadrilateralBound D) :
    mean D (r + s) ≤ mean D r + mean D s := by
  have htotal : 0 ≤ ∑ g : GL m, deficit D (g • a) (g • b) (g • c) (g • d) :=
    Finset.sum_nonneg (fun _ _ => sub_nonneg.mpr (h _ _ _ _))
  rw [sq.sum_deficit D] at htotal
  have hcard : (0 : ℝ) < Fintype.card (GL m) := Nat.cast_pos.mpr Fintype.card_pos
  have := nonneg_of_mul_nonneg_left htotal hcard
  linarith

/-- When the pair means saturate subadditivity, each such quadrilateral
saturates the inequality pointwise. -/
theorem IsSquare.eq_of_mean_eq_add {a b c d : Plane m} (sq : IsSquare r s a b c d)
    {D : Plane m → Plane m → ℝ} (h : QuadrilateralBound D)
    (heq : mean D (r + s) = mean D r + mean D s) :
    D a c + D b d = D a b + D b c + D c d + D d a := by
  have htotal := sq.sum_deficit D
  rw [heq, sub_self, mul_zero, zero_mul] at htotal
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ =>
    show 0 ≤ deficit D (g • a) (g • b) (g • c) (g • d) from sub_nonneg.mpr (h _ _ _ _))).mp htotal
  simpa [deficit, sub_eq_zero, eq_comm] using hzero (1 : GL m) (Finset.mem_univ _)

/-- Type zero consists of the diagonal of the Grassmannian. -/
theorem HasType.eq_of_zero {a b : Plane m} (h : HasType 0 a b) : a = b := by
  have h' : Module.finrank (ZMod 2) (a.val ⊔ b.val : Submodule (ZMod 2) (Space m)) = m := h
  have ha : a.val = a.val ⊔ b.val :=
    Submodule.eq_of_le_of_finrank_eq le_sup_left (by rw [plane_finrank, h'])
  have hb : b.val = a.val ⊔ b.val :=
    Submodule.eq_of_le_of_finrank_eq le_sup_right (by rw [plane_finrank, h'])
  exact Subtype.ext (ha.trans hb.symm)

theorem mean_zero {D : Plane m → Plane m → ℝ} (h : ∀ a, D a a = 0) : mean D 0 = 0 := by
  have hz (p : Pair m 0) : D p.val.1 p.val.2 = 0 := p.property.eq_of_zero ▸ h _
  simp [mean, hz]

/-- Grassmannian pair means are subadditive up to the maximum type. -/
theorem mean_add_le {D : Plane m → Plane m → ℝ} (h : QuadrilateralBound D) (hrs : r + s ≤ m) :
    mean D (r + s) ≤ mean D r + mean D s := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd⟩ := exists_square hrs
  exact IsSquare.mean_add_le (⟨hab, hbc, hcd, hda, hac, hbd⟩ : IsSquare r s a b c d) h

theorem mean_le_mul_one {D : Plane m → Plane m → ℝ} (h : QuadrilateralBound D)
    (hzero : ∀ a, D a a = 0) (hr : r ≤ m) : mean D r ≤ r * mean D 1 := by
  induction r with
  | zero => simp [mean_zero hzero]
  | succ k ih =>
    have ha := mean_add_le h hr
    rw [Nat.cast_succ, add_mul, one_mul]
    exact ha.trans (add_le_add_left (ih (by omega)) _)

/-- Saturation between adjacent and complementary pairs forces saturation at
every intermediate type. -/
theorem mean_eq_mul_one {D : Plane m → Plane m → ℝ} (h : QuadrilateralBound D)
    (hzero : ∀ a, D a a = 0) (hfull : mean D m = m * mean D 1) (hr : r ≤ m) :
    mean D r = r * mean D 1 := by
  apply le_antisymm (mean_le_mul_one h hzero hr)
  have hsplit := mean_add_le h (Nat.le_of_eq (Nat.add_sub_of_le hr))
  rw [Nat.add_sub_of_le hr, hfull] at hsplit
  have htail := mean_le_mul_one h hzero (Nat.sub_le m r)
  rw [Nat.cast_sub hr, sub_mul] at htail
  linarith

/-- Section 5.1's `Bᵣ` for a map of the Grassmannian into a metric space. -/
noncomputable def energy {X : Type*} [PseudoMetricSpace X] (f : Plane m → X) (r : ℕ) : ℝ :=
  mean (fun a b => dist (f a) (f b) ^ 2) r

theorem energy_add_le {X : Type*} [PseudoMetricSpace X] (h : SpectralGeometry.HasCATZeroSegments X)
    (f : Plane m → X) (hrs : r + s ≤ m) : energy f (r + s) ≤ energy f r + energy f s :=
  mean_add_le (fun a b c d => SpectralGeometry.quadrilateral_sq h (f a) (f b) (f c) (f d)) hrs

theorem energy_le_mul_one {X : Type*} [PseudoMetricSpace X]
    (h : SpectralGeometry.HasCATZeroSegments X) (f : Plane m → X) (hr : r ≤ m) :
    energy f r ≤ r * energy f 1 :=
  mean_le_mul_one (fun a b c d => SpectralGeometry.quadrilateral_sq h (f a) (f b) (f c) (f d))
    (by simp) hr

end Grassmann

end VPVNP
end Computability
end OAI
