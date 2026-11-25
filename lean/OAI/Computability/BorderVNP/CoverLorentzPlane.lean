import OAI.Computability.BorderVNP.CoverLorentzFrames
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# Proper and cocompact congruence actions on the hyperbolic plane

The geometric tile host in §5.1 uses the curvature-minus-one upper half-plane.
The integral matrix representation acts properly, cocompactly and freely at
every positive level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set UpperHalfPlane
open scoped MatrixGroups Pointwise

/-- The integral units at a level taking some point of `A` into `B`. -/
def movers (l : ℕ) (A B : Set ℍ) : Set (gamma l) :=
  {u | ((gammaSL l u) • A ∩ B).Nonempty}

/-- Properness of the real special-linear action and discreteness of the quaternion order give
finitely many possible translates intersecting any two fixed compact regions. -/
theorem finite_movers (l : ℕ) {A B : Set ℍ} (hA : IsCompact A) (hB : IsCompact B) :
    (movers l A B).Finite := by
  let S := {g : SL(2,ℝ) | (g • A ∩ B).Nonempty}
  have hc : IsCompact S := ProperSMul.isCompact_setOfPred_inter_nonempty hA hB
  let v (u : gamma l) := u.val.val
  have hi : Function.Injective v := Units.val_injective.comp Subtype.val_injective
  apply ((split_preimage_compact_finite (hc.image continuous_subtype_val)).preimage hi.injOn).subset
  intro u hu
  exact ⟨gammaSL l u,hu,rfl⟩

/-- Freeness of the action of each positive congruence level. -/
theorem eq_one_of_fix {l : ℕ} (u : gamma (l+1)) (z : ℍ) (hf : gammaSL (l+1) u • z = z) :
    u = 1 := by
  classical
  have hpow (k : ℕ) : gammaSL (l+1) (u^k) • z = z := by
    induction k with
    | zero => simp
    | succ k h => rw [pow_succ,map_mul,mul_smul,hf,h]
  have hfins := finite_movers (l+1) (isCompact_singleton (x := z)) (isCompact_singleton (x := z))
  let := hfins.fintype
  let f (k : ℕ) : movers (l+1) {z} {z} :=
    ⟨u^k, z, ⟨z,rfl,hpow k⟩,rfl⟩
  have hfin : IsOfFinOrder u := by
    by_contra hn
    apply not_injective_infinite_finite f
    intro i j hij
    exact (injective_pow_iff_not_isOfFinOrder.mpr hn) (congrArg Subtype.val hij)
  obtain ⟨k,hk,he⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  apply Subtype.ext
  exact eq_one_of_finite_order (gamma_le_one l u.2)
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨k,hk,congrArg Subtype.val he⟩)

/-- In particular no central sign is collapsed on passing to the projective special linear group. -/
theorem gammaPSL_injective (l : ℕ) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center SL(2,ℝ))).comp (gammaSL (l+1))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro u hu
  have hc : gammaSL (l+1) u ∈ Subgroup.center SL(2,ℝ) := (QuotientGroup.eq_one_iff _).mp hu
  obtain ⟨a,ha,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hg : (gammaSL (l+1) u)^2 = 1 := by
    apply Subtype.ext
    change ((gammaSL (l+1) u).val)^2 = (1 : Mat)
    rw [← he,← map_pow]
    have h2 : a^2 = 1 := by simpa using ha
    rw [h2,map_one]
  have hpow : u^2 = 1 := gammaSL_injective _ (by rw [map_pow,hg,map_one])
  exact Subtype.ext (eq_one_of_finite_order (gamma_le_one l u.2)
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,congrArg Subtype.val hpow⟩))

/-- Every point lies within one uniform radius of some translate of the base site. -/
theorem orbit_covers_balls (l : ℕ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℍ,
    ∃ u : gamma l, dist z (gammaSL l u • I) ≤ R := by
  obtain ⟨K,hK,hmeet⟩ := exists_compact_representatives l
  have hi : IsCompact ((fun g : SL(2,ℝ) => g • I) '' K) := hK.image (by fun_prop)
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall I).mp hi.isBounded
  refine ⟨max r 0,le_max_right _ _,?_⟩
  intro z
  obtain ⟨u,hu⟩ := hmeet z.toSL2R
  have hm := hr ⟨gammaSL l u * z.toSL2R,hu,rfl⟩
  change dist ((gammaSL l u * z.toSL2R) • I) I ≤ r at hm
  rw [mul_smul,toSL2R_smul_I] at hm
  refine ⟨u⁻¹,?_⟩
  rw [← dist_smul (gammaSL l u) z, map_inv,smul_inv_smul]
  exact hm.trans (le_max_left _ _)

/-- A compact set of plane points has only finitely many orbit-site addresses. -/
theorem finite_sites (l : ℕ) {K : Set ℍ} (hK : IsCompact K) :
    {u : gamma l | gammaSL l u • I ∈ K}.Finite :=
  (finite_movers l (isCompact_singleton (x := I)) hK).subset
    (fun u hu => ⟨gammaSL l u • I,⟨I,rfl,rfl⟩,hu⟩)

/-- The closed Dirichlet tile about the base site. Boundary ties are included. -/
def dirichlet (l : ℕ) : Set ℍ := {z | ∀ u : gamma l, dist z I ≤ dist z (gammaSL l u • I)}

/-- The closed tile is contained in a uniform ball. -/
theorem dirichlet_bounded (l : ℕ) : ∃ R : ℝ, 0 ≤ R ∧ dirichlet l ⊆ Metric.closedBall I R := by
  obtain ⟨R,hR,hc⟩ := orbit_covers_balls l
  refine ⟨R,hR,?_⟩
  intro z hz
  obtain ⟨u,hu⟩ := hc z
  exact (hz u).trans hu

/-- Compactness of each closed Dirichlet tile in the hyperbolic metric. -/
theorem dirichlet_compact (l : ℕ) : IsCompact (dirichlet l) := by
  obtain ⟨R,_,h⟩ := dirichlet_bounded l
  apply (ProperSpace.isCompact_closedBall I R).of_isClosed_subset _ h
  rw [show dirichlet l = ⋂ u : gamma l, {z : ℍ | dist z I ≤ dist z (gammaSL l u • I)} by
    ext z; simp [dirichlet]]
  exact isClosed_iInter (fun _ => isClosed_le (by fun_prop) (by fun_prop))

/-- Every orbit meets the compact tile, by minimizing over finitely many possible nearest sites. -/
theorem exists_mem_dirichlet (l : ℕ) (z : ℍ) : ∃ u : gamma l, gammaSL l u • z ∈ dirichlet l := by
  classical
  let K := Metric.closedBall z (dist z I)
  have hfin := finite_sites l (ProperSpace.isCompact_closedBall z (dist z I))
  let s := hfin.toFinset
  have hone : (1 : gamma l) ∈ s := by
    apply hfin.mem_toFinset.mpr
    simp [Metric.mem_closedBall,dist_comm]
  obtain ⟨u,hu,hmin⟩ := s.exists_min_image (fun v => dist z (gammaSL l v • I)) ⟨1,hone⟩
  have best (v : gamma l) : dist z (gammaSL l u • I) ≤ dist z (gammaSL l v • I) := by
    by_cases hv : v ∈ s
    · exact hmin v hv
    · have hv' : ¬ dist z (gammaSL l v • I) ≤ dist z I := by
        intro he
        apply hv
        exact hfin.mem_toFinset.mpr (by simpa [Metric.mem_closedBall,dist_comm] using he)
      have he := hmin 1 hone
      simp only [map_one,one_smul] at he
      exact he.trans (le_of_not_ge hv')
  refine ⟨u⁻¹,?_⟩
  intro v
  rw [← dist_smul (gammaSL l u) (gammaSL l u⁻¹ • z),map_inv,smul_inv_smul]
  rw [← dist_smul (gammaSL l u) ((gammaSL l u)⁻¹ • z),smul_inv_smul,← mul_smul,← map_mul]
  exact best (u*v)

end Cover

end BorderVNP
end Computability
end OAI
