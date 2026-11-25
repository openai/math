import OAI.Computability.VPVNP.GrassmannCompactness
import Mathlib.Tactic

namespace OAI
/-! # Typewise means of CAT(0) arrays on middle-dimensional planes -/

namespace Hierarchy.GrassmannAverages

open Computability.VPVNP.Grassmann
open scoped BigOperators

private theorem sum_action {G Y : Type*} [Group G] [Fintype G] [Fintype Y] [MulAction G Y]
    (trans : ∀ p q : Y, ∃ g : G, g • p = q) (u : Y → ℝ) (p : Y) :
    ∑ g : G, u (g • p) = (Fintype.card G : ℝ) * ((∑ q, u q) / Fintype.card Y) := by
  let _ : Nonempty Y := ⟨p⟩
  have hp (q : Y) : ∑ g : G, u (g • q) = ∑ g : G, u (g • p) := by
    obtain ⟨k,rfl⟩ := trans p q
    simpa only [← mul_smul, Equiv.coe_mulRight] using Equiv.sum_comp (Equiv.mulRight k) (fun g : G => u (g • p))
  have hq (g : G) : ∑ q : Y, u (g • q) = ∑ q, u q := Equiv.sum_comp (MulAction.toPerm g) u
  have ht : (Fintype.card Y : ℝ) * (∑ g : G, u (g • p)) =
      (Fintype.card G : ℝ) * ∑ q, u q := by
    calc
      _ = ∑ q : Y, ∑ g : G, u (g • q) := by simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ g : G, ∑ q : Y, u (g • q) := Finset.sum_comm
      _ = _ := by simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hy : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hy]
  linarith only [ht]

theorem sum_translates {m r : ℕ} (trans : ∀ r, ∀ p q : Pair m r, ∃ g : Computability.VPVNP.Grassmann.GL m, g • p = q) (D : Plane m → Plane m → ℝ) {a b : Plane m}
    (h : HasType r a b) : ∑ g : Computability.VPVNP.Grassmann.GL m, D (g • a) (g • b) = Fintype.card (Computability.VPVNP.Grassmann.GL m) * mean D r :=
  sum_action (trans r) (fun p : Pair m r => D p.val.1 p.val.2) ⟨(a,b),h⟩

private def defect {m : ℕ} (D : Plane m → Plane m → ℝ) (a b c d : Plane m) (g : Computability.VPVNP.Grassmann.GL m) :=
  D (g • a) (g • b) + D (g • b) (g • c) + D (g • c) (g • d) + D (g • d) (g • a) -
    (D (g • a) (g • c) + D (g • b) (g • d))

private theorem sum_defect {m r s : ℕ} (trans : ∀ r, ∀ p q : Pair m r, ∃ g : Computability.VPVNP.Grassmann.GL m, g • p = q) (D : Plane m → Plane m → ℝ) {a b c d : Plane m}
    (q : IsSquare r s a b c d) :
    ∑ g : Computability.VPVNP.Grassmann.GL m, defect D a b c d g =
      2 * (Fintype.card (Computability.VPVNP.Grassmann.GL m) : ℝ) * (mean D r + mean D s - mean D (r+s)) := by
  unfold defect
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_translates trans D q.ab,
    sum_translates trans D q.bc, sum_translates trans D q.cd, sum_translates trans D q.da,
    sum_translates trans D q.ac, sum_translates trans D q.bd]
  ring

theorem subadditive {m r s : ℕ} (trans : ∀ r, ∀ p q : Pair m r, ∃ g : Computability.VPVNP.Grassmann.GL m, g • p = q) {D : Plane m → Plane m → ℝ} (hD : QuadBounds D)
    {a b c d : Plane m} (q : IsSquare r s a b c d) : mean D (r+s) ≤ mean D r + mean D s := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun (g : Computability.VPVNP.Grassmann.GL m) _ => sub_nonneg.mpr (hD.quad (g•a) (g•b) (g•c) (g•d)))
  change 0 ≤ ∑ g : Computability.VPVNP.Grassmann.GL m, defect D a b c d g at h
  rw [sum_defect trans D q] at h
  have hg : 0 < (Fintype.card (Computability.VPVNP.Grassmann.GL m) : ℝ) := by exact_mod_cast Fintype.card_pos
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h (by positivity))

theorem opposite {m r s : ℕ} (trans : ∀ r, ∀ p q : Pair m r, ∃ g : Computability.VPVNP.Grassmann.GL m, g • p = q) {D : Plane m → Plane m → ℝ} (hD : QuadBounds D)
    {a b c d : Plane m} (q : IsSquare r s a b c d) (heq : mean D (r+s) = mean D r + mean D s) :
    D a b = D c d ∧ D b c = D d a := by
  have h (g : Computability.VPVNP.Grassmann.GL m) : 0 ≤ defect D a b c d g := sub_nonneg.mpr (hD.quad _ _ _ _)
  have hz := sum_defect trans D q
  rw [heq, sub_self, mul_zero] at hz
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => h g)).mp hz (1 : Computability.VPVNP.Grassmann.GL m) (Finset.mem_univ _)
  apply hD.opposite
  simpa [defect, sub_eq_zero, eq_comm] using hh

private theorem mean_zero {m : ℕ} {D : Plane m → Plane m → ℝ} (hD : QuadBounds D) : mean D 0 = 0 := by
  have hp (p : Pair m 0) : p.val.1 = p.val.2 := by
    have hh : Module.finrank (ZMod 2) (p.val.1.val ⊔ p.val.2.val : Submodule _ _) = m := p.property
    apply Subtype.ext
    exact (Submodule.eq_of_le_of_finrank_eq le_sup_left (p.val.1.property.trans hh.symm)).trans
      (Submodule.eq_of_le_of_finrank_eq le_sup_right (p.val.2.property.trans hh.symm)).symm
  have zero (p : Pair m 0) : D p.val.1 p.val.2 = 0 := by rw [hp p,hD.diag]
  simp only [mean, zero, Finset.sum_const_zero, zero_div]

/-- A square for each admissible split suffices for all Grassmann mean bounds. -/
theorem mean_le {m : ℕ} (trans : ∀ r, ∀ p q : Pair m r, ∃ g : Computability.VPVNP.Grassmann.GL m, g • p = q) (squares : ∀ r s, r+s ≤ m → ∃ a b c d : Plane m, IsSquare r s a b c d)
    {D : Plane m → Plane m → ℝ} (hD : QuadBounds D) (r : ℕ) (hr : r ≤ m) :
    mean D r ≤ r * mean D 1 := by
  induction r with
  | zero => simp [mean_zero hD]
  | succ r ih =>
    obtain ⟨a,b,c,d,hq⟩ := squares r 1 hr
    have h := subadditive trans hD hq
    have h' := ih (by omega)
    push_cast
    linarith only [h, h']

/-- Saturation at the maximum distance class implies saturation in each class. -/
theorem mean_eq {m : ℕ} (trans : ∀ r, ∀ p q : Pair m r, ∃ g : Computability.VPVNP.Grassmann.GL m, g • p = q) (squares : ∀ r s, r+s ≤ m → ∃ a b c d : Plane m, IsSquare r s a b c d)
    {D : Plane m → Plane m → ℝ} (hD : QuadBounds D) (h1 : mean D 1 = 1) (hm : mean D m = m)
    (r : ℕ) (hr : r ≤ m) : mean D r = r := by
  have hu (t : ℕ) (ht : t ≤ m) : mean D t ≤ t := by simpa [h1] using mean_le trans squares hD t ht
  obtain ⟨a,b,c,d,hq⟩ := squares r (m-r) (by omega)
  have ha := subadditive trans hD hq
  rw [Nat.add_sub_of_le hr, hm] at ha
  have hb := hu (m-r) (by omega)
  rw [Nat.cast_sub hr] at hb
  exact le_antisymm (hu r hr) (by linarith)

end Hierarchy.GrassmannAverages

end OAI
