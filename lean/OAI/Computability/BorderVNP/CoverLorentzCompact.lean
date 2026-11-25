import OAI.Computability.BorderVNP.CoverLorentzMinkowski

/-!
# Compact reduction for the congruence groups

The matrices found by Minkowski have determinants in a fixed finite interval.
For each determinant and congruence residue choose one integral quaternion with
these invariants. Division by this fixed representative gives a norm-one
integral unit at the required level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set
open scoped Matrix

private theorem norm_bounded {x : Order} {g : Mat} (hg : g.det = 1)
    (h : ∀ i j, |(split x*g) i j| ≤ 3) : |norm x| ≤ 18 := by
  have hmul (a b c d : Fin 2) : |(split x*g) a b * (split x*g) c d| ≤ 9 := by
    rw [abs_mul]
    exact le_trans (mul_le_mul (h a b) (h c d) (abs_nonneg _) (by norm_num)) (by norm_num)
  have habs : |(norm x : ℝ)| ≤ 18 := calc
    _ = |(split x*g).det| := by rw [Matrix.det_mul, hg, mul_one, det_split]
    _ ≤ _ := by
      rw [Matrix.det_fin_two]
      exact (abs_sub _ _).trans (by linarith [hmul 0 0 1 1,hmul 0 1 1 0])
  exact_mod_cast habs

private theorem norm_unit_factor {x₀ x z : Order} (l : ℕ) (h0 : norm x₀ ≠ 0)
    (he : norm x = norm x₀) (hz : x = x₀ + ((7:ℤ)^l * norm x₀) • z) :
    ∃ u : gamma l, x₀ * (u.val : Order) = x := by
  let a := atDepth l (star x₀*z)
  have hstar : x₀*star x₀ = QuaternionAlgebra.coe (norm x₀) := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    rcases x₀ with ⟨r,i,j,k⟩
    simp only [QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, norm]
    ring
  have hmul : x₀ * a = x := by
    rw [hz]
    simp only [a,atDepth,mul_add,mul_one,mul_smul_comm,← mul_assoc x₀ (star x₀),
      hstar, QuaternionAlgebra.coe_mul_eq_smul, smul_smul]
  have ha : norm a = 1 := by
    have h := congrArg norm hmul
    rw [norm_mul,he] at h
    exact (mul_eq_left₀ h0).1 h
  exact ⟨⟨normUnit a ha, ha, _,rfl⟩,hmul⟩

private def modCoords (m : ℕ) (x : Order) : Fin 4 → ZMod m :=
  fun i => (↑(![x.re, x.imI, x.imJ, x.imK] i) : ZMod m)

private theorem common_factor {l m : ℕ} {x₀ x : Order} (h0 : norm x₀ ≠ 0)
    (he : norm x = norm x₀) (hm : (7:ℤ)^l * norm x₀ ∣ (m:ℤ))
    (hr : modCoords m x₀ = modCoords m x) : ∃ u : gamma l, x₀*(u.val : Order) = x := by
  have h (i : Fin 4) : (m:ℤ) ∣
      (![x.re, x.imI, x.imJ, x.imK] i - ![x₀.re, x₀.imI, x₀.imJ, x₀.imK] i) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1
    exact congrFun hr i
  obtain ⟨r,hr⟩ := hm.trans (h 0)
  obtain ⟨i,hi⟩ := hm.trans (h 1)
  obtain ⟨j,hj⟩ := hm.trans (h 2)
  obtain ⟨k,hk⟩ := hm.trans (h 3)
  exact norm_unit_factor l h0 he (z := ⟨r,i,j,k⟩) (QuaternionAlgebra.ext
    (by change x.re = x₀.re + (7^l * norm x₀)*r; linarith only [show x.re - x₀.re = _ from hr])
    (by change x.imI = x₀.imI + (7^l * norm x₀)*i; linarith only [show x.imI - x₀.imI = _ from hi])
    (by change x.imJ = x₀.imJ + (7^l * norm x₀)*j; linarith only [show x.imJ - x₀.imJ = _ from hj])
    (by change x.imK = x₀.imK + (7^l * norm x₀)*k; linarith only [show x.imK - x₀.imK = _ from hk]))

/-- A single compact set meets every left orbit of the represented level group in `SL₂(ℝ)`. -/
theorem exists_compact_representatives (l : ℕ) :
    ∃ K : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ), IsCompact K ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ u : gamma l, gammaSL l u * g ∈ K := by
  classical
  let m := 7^l * Nat.factorial 18
  have hm : m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.factorial_pos _))
  have : NeZero m := ⟨hm⟩
  let Good := {x : Order // x ≠ 0 ∧ |norm x| ≤ 18}
  let key (x : Good) : Icc (-18:ℤ) 18 × (Fin 4 → ZMod m) :=
    (⟨norm x.val, abs_le.mp x.2.2⟩, modCoords m x.val)
  let rep (t : range key) := t.2.choose
  have hrep (t : range key) : key (rep t) = t.val := t.2.choose_spec
  let box : Set Mat := Set.pi univ (fun _ => Set.pi univ (fun _ => Icc (-3:ℝ) 3))
  have hc : IsCompact box := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  let S : Set Mat := ⋃ t : range key, (fun y : Mat => (split (rep t).val)⁻¹ * y) '' box
  have hS : IsCompact S := isCompact_iUnion (fun t => hc.image (by fun_prop :
    Continuous fun y : Mat => (split (rep t).val)⁻¹ * y))
  refine ⟨Subtype.val ⁻¹' S, Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hS,?_⟩
  intro g
  obtain ⟨x,hx,hb⟩ := exists_bounded_translate g.val g.property
  let w : Good := ⟨x,hx,norm_bounded g.property hb⟩
  let t : range key := ⟨key w,w,rfl⟩
  let x₀ := (rep t).val
  have hnorm : norm x₀ = norm x := congrArg (fun t => t.1.val) (hrep t)
  have hr : modCoords m x₀ = modCoords m x := congrArg Prod.snd (hrep t)
  have hn : norm x₀ ≠ 0 := fun h => (rep t).2.1 (eq_zero_of_norm_eq_zero _ h)
  have hdvd : norm x₀ ∣ (Nat.factorial 18 : ℤ) := by
    apply Int.dvd_natCast.mpr
    have ha : (norm x₀).natAbs ≤ 18 := by
      have hh : ((norm x₀).natAbs : ℤ) ≤ 18 := by simpa only [Int.natCast_natAbs] using (rep t).2.2
      exact_mod_cast hh
    exact Nat.dvd_factorial (Int.natAbs_pos.mpr hn) ha
  obtain ⟨u,hu⟩ := common_factor hn hnorm.symm (m := m) (l := l)
    (by simpa only [m,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      mul_dvd_mul_left ((7:ℤ)^l) hdvd) hr
  refine ⟨u, mem_iUnion.mpr ⟨t, split x * g.val, ?_, ?_⟩⟩
  · exact fun i _ j _ => abs_le.mp (hb i j)
  · have hu' := congrArg split hu
    rw [map_mul] at hu'
    change (split x₀)⁻¹ * (split x * g.val) = split u.val.val * g.val
    rw [← hu',← mul_assoc,← mul_assoc,Matrix.nonsing_inv_mul,one_mul]
    rw [det_split,isUnit_iff_ne_zero]
    exact_mod_cast hn

end Cover

end BorderVNP
end Computability
end OAI
