import OAI.Computability.BorderVNP.CoverHeckeRotation
import OAI.Computability.BorderVNP.CoverHeckeCorrespondenceWords
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Denominators and congruence levels in the quaternion frame motions

The rational element of §5.2 and its inverse have denominator seven. Products
add denominator exponents, and conjugation can use the denominator twice.
Consequently the images of level `l+2a` under such conjugation land in level `l`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open Matrix BorderVNP.Hecke
open scoped Matrix

/-- Multiplying a motion and its inverse by `7^a` gives integral quaternions. -/
def Clears (g : SL) (a : ℕ) : Prop :=
  (∃ x : Order, (7:ℝ)^a • (g : Mat) = split x) ∧
    (∃ y : Order, (7:ℝ)^a • ((g⁻¹ : SL) : Mat) = split y)

/-- Inversion preserves the same denominator exponent. -/
theorem Clears.inv {g : SL} {a : ℕ} (h : Clears g a) : Clears g⁻¹ a :=
  ⟨h.2, by simpa using h.1⟩

/-- Multiplying motions adds the two denominator exponents. -/
theorem Clears.mul {g h : SL} {a b : ℕ} (hg : Clears g a) (hh : Clears h b) :
    Clears (g*h) (a+b) := by
  rcases hg with ⟨⟨s,hs⟩,⟨s',hs'⟩⟩
  rcases hh with ⟨⟨t,ht⟩,⟨t',ht'⟩⟩
  refine ⟨⟨s*t, ?_⟩, ⟨t'*s', ?_⟩⟩
  · change (7:ℝ)^(a+b) • ((g : Mat)*(h : Mat)) = _
    rw [map_mul,← hs,← ht,pow_add,smul_mul_assoc,mul_smul_comm,smul_smul]
  · rw [_root_.mul_inv_rev]
    change (7:ℝ)^(a+b) • (((h⁻¹:SL):Mat)*((g⁻¹:SL):Mat)) = _
    rw [map_mul,← ht',← hs',pow_add,smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm ((7:ℝ)^a)]

/-- The lattice elements and their inverses are integral. -/
theorem clears_lattice (d : ℕ) {g : SL} (hg : g ∈ (gammaSL d).range) : Clears g 0 := by
  obtain ⟨u, rfl⟩ := hg
  refine ⟨⟨u.val.val, by simp; rfl⟩, ⟨u⁻¹.val.val, ?_⟩⟩
  rw [pow_zero,one_smul,← map_inv]
  rfl

/-- The denominator of the elliptic quaternion and its conjugate is at most seven. -/
theorem clears_elliptic : Clears elliptic 1 := by
  refine ⟨⟨_, by simpa using elliptic_numerator⟩, ⟨⟨-5,0,0,-2⟩, ?_⟩⟩
  rw [pow_one]
  change (7:ℝ) • (((rotation _)⁻¹ : SL) : Mat) = _
  rw [← rotation_neg]
  have h := elliptic_numerator
  ext i j
  have he := congrArg (fun M : Mat => M i j) h
  fin_cases i <;> fin_cases j <;> simp [elliptic,rotation,split, neg_div] at he ⊢ <;> linarith

/-- The level represented in the frame group. -/
noncomputable abbrev lattice (d : ℕ) : Subgroup SL := (gammaSL d).range

private theorem split_depth (d : ℕ) (b : Order) :
    split (atDepth d b) = 1 + (7:ℝ)^d • split b := by
  simp only [atDepth,map_add,map_one,map_zsmul]
  ext i j
  simp [← Int.cast_smul_eq_zsmul ℝ]

/-- Two occurrences of the denominator suffice for conjugation of every element of
the deeper congruence subgroup. -/
theorem conjugate_lattice {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ)
    {u : SL} (hu : u ∈ lattice (d+2*a)) : g*u*g⁻¹ ∈ lattice d := by
  obtain ⟨v,rfl⟩ := hu
  obtain ⟨⟨s,hs⟩,⟨t,ht⟩⟩ := hg
  obtain ⟨_, b, hb⟩ := v.property
  let x := atDepth d (s*b*t)
  have hm : split x = ((g * gammaSL (d+2*a) v * g⁻¹ : SL) : Mat) := by
    change split (atDepth d (s*b*t)) = (g : Mat) * split v.val.val * ((g⁻¹ : SL) : Mat)
    rw [hb,split_depth,split_depth,map_mul,map_mul,← hs,← ht]
    have h1 : (g : Mat) * ((g⁻¹ : SL) : Mat) = 1 := congrArg (fun a : SL => (a : Mat)) (mul_inv_cancel g)
    simp only [mul_add, add_mul, mul_one, h1, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    rw [pow_add, two_mul, pow_add]
  have hn : norm x = 1 := by
    have hd := det_split x
    rw [hm,(g * gammaSL (d+2*a) v * g⁻¹).property] at hd
    exact_mod_cast hd.symm
  exact ⟨⟨normUnit x hn,hn,s*b*t,rfl⟩,Subtype.ext hm⟩

/-- A chosen Hecke step uses just one denominator seven. -/
theorem clears_step (i : Cosets (intersection (lattice 1) elliptic)) :
    Clears (step (lattice 1) elliptic i) 1 := by
  exact clears_elliptic.mul (clears_lattice 1 i.out.property)

/-- A motion sampled from the j-fold operator uses denominator at most `7^j`. -/
theorem clears_motion (j : ℕ) (w : Fin j → Cosets (intersection (lattice 1) elliptic)) :
    Clears (motion (step (lattice 1) elliptic) j w) j := by
  induction j with
  | zero => exact clears_lattice 1 (Subgroup.one_mem _)
  | succ j ih => exact (ih _).mul (clears_step _)

/-- The subgroup indexing the Hecke branches has finite index for a motion with denominator seven. -/
theorem finite_intersection_of_clears {g : SL} (hg : Clears g 1) :
    Finite (Cosets (intersection (lattice 1) g)) := by
  let e : gamma 1 ≃* lattice 1 := MonoidHom.ofInjective (gammaSL_injective 1)
  let S := (gamma 3).subgroupOf (gamma 1)
  have hs : S.FiniteIndex := by
    constructor
    change tileCount 3 ≠ 0
    rw [tileCount_eq 1]
    exact mul_ne_zero (by norm_num) tileCount_two_bounds.1.ne'
  have hm : (S.map e.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective S e.surjective
  have hle : S.map e.toMonoidHom ≤ intersection (lattice 1) g := by
    rintro _ ⟨a, ha, rfl⟩
    change g * gammaSL 1 a * g⁻¹ ∈ lattice 1
    apply conjugate_lattice hg 1
    exact ⟨⟨a.val,ha⟩, rfl⟩
  let : (intersection (lattice 1) g).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel _).symm

/-- Both correspondence indices for the specific quaternion are finite. -/
theorem finite_elliptic_indices :
    Finite (Cosets (intersection (lattice 1) elliptic)) ∧
      Finite (Cosets (intersection (lattice 1) elliptic⁻¹)) :=
  ⟨finite_intersection_of_clears clears_elliptic, finite_intersection_of_clears clears_elliptic.inv⟩

/-- Any larger common denominator exponent also clears the motion. -/
theorem Clears.mono {g : SL} {a b : ℕ} (h : Clears g a) (hle : a ≤ b) : Clears g b := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hle
  have hc {M : Mat} {s : Order} (hs : (7:ℝ)^a • M = split s) :
      ∃ x : Order, (7:ℝ)^(a+c) • M = split x := by
    refine ⟨(7:ℤ)^c • s, ?_⟩
    rw [map_zsmul, ← hs, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, pow_add]
    push_cast
    rw [mul_comm]
  exact ⟨h.1.elim fun _ hs => hc hs, h.2.elim fun _ hs => hc hs⟩

/-- Mapping a lattice and motion through a homomorphism preserves finiteness of
the set of Hecke branches, including when the map has a central kernel. -/
theorem finite_map_branches {G P : Type*} [Group G] [Group P] (Γ : Subgroup G) (z : G)
    (p : G →* P) [Finite (Cosets (intersection Γ z))] :
    Finite (Cosets (intersection (Γ.map p) (p z))) := by
  let S := intersection Γ z
  have hq : Finite (Γ ⧸ S) := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)
  have hs : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hm : (S.map (p.subgroupMap Γ)).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective S (p.subgroupMap_surjective Γ)
  have hle : S.map (p.subgroupMap Γ) ≤ intersection (Γ.map p) (p z) := by
    rintro _ ⟨a, ha, rfl⟩
    change p z * p a.val * (p z)⁻¹ ∈ Γ.map p
    exact ⟨z*a.val*z⁻¹,ha,by simp⟩
  let : (intersection (Γ.map p) (p z)).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel _).symm

/-- Projection from the double cover to the actual projective frame group. -/
abbrev project : SL →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ :=
  QuotientGroup.mk' (Subgroup.center SL)

/-- The integral lattice and its projective image are countable. -/
theorem countable_projective_lattice (d : ℕ) : Countable ((lattice d).map project) := by
  let : Countable Order := (QuaternionAlgebra.equivProd (2:ℤ) 0 3).injective.countable
  let : Countable Orderˣ := Units.val_injective.countable
  let : Countable (lattice d) := (gammaSL d).rangeRestrict_surjective.countable
  exact (project.subgroupMap_surjective _).countable

/-- Finite degree of both projective frame correspondences for the quaternion. -/
theorem finite_projective_indices :
    Finite (Cosets (intersection ((lattice 1).map project) (project elliptic))) ∧
    Finite (Cosets (intersection ((lattice 1).map project) (project elliptic)⁻¹)) := by
  have h₁ := finite_elliptic_indices.1
  have h₂ := finite_elliptic_indices.2
  exact ⟨finite_map_branches _ _ project, by
    rw [← map_inv]
    exact finite_map_branches _ _ project⟩

/-- Every sample in the projective frame correspondence lifts to a rational motion
with both denominators bounded by the common averaging length exponent. -/
theorem lift_projective_sample (n : ℕ)
    (s : Samples (Cosets (intersection ((lattice 1).map project) (project elliptic))) n) :
    ∃ g : SL, Clears g n ∧ project g =
      motion (step ((lattice 1).map project) (project elliptic)) s.1.val s.2 := by
  let I := Cosets (intersection ((lattice 1).map project) (project elliptic))
  have letters (i : I) : ∃ g : SL, Clears g 1 ∧
      project g = step ((lattice 1).map project) (project elliptic) i := by
    obtain ⟨v,hv,e⟩ := i.out.property
    exact ⟨elliptic*v,clears_elliptic.mul (clears_lattice 1 hv),by rw [map_mul,e]; rfl⟩
  have words (j : ℕ) (w : Fin j → I) : ∃ g : SL, Clears g j ∧ project g =
      motion (step ((lattice 1).map project) (project elliptic)) j w := by
    induction j with
    | zero => exact ⟨1, clears_lattice 1 (Subgroup.one_mem _), map_one project⟩
    | succ j ih =>
      obtain ⟨g,hg,eg⟩ := ih (Fin.tail w)
      obtain ⟨v,hv,ev⟩ := letters (w 0)
      exact ⟨g*v,hg.mul hv,by rw [map_mul,eg,ev]; rfl⟩
  obtain ⟨g,h,e⟩ := words s.1.val s.2
  exact ⟨g,h.mono (Nat.le_of_lt_succ s.1.isLt),e⟩

end Cover.Frame

end BorderVNP
end Computability
end OAI
