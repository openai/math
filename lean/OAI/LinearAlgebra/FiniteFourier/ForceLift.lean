import OAI.LinearAlgebra.FiniteFourier.ForceSupport

/-! # Lifting a force through a two-phase contraction

Hahn–Banach extends the boundary force from pairs of placements agreeing
on both internal wires. Testing the extended functional on one phase at a
time gives forces for both phases, and testing on glued legs gives cancellation.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped InnerProductSpace BigOperators
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private abbrev Placement (E : Type*) := Fin 4 → E

private def glued (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Submodule ℝ (Placement E × Placement E) where
  carrier := {x | x.1 2 = x.2 0 ∧ x.1 3 = x.2 1}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun hx hy ↦ ⟨congrArg₂ (· + ·) hx.1 hy.1, congrArg₂ (· + ·) hx.2 hy.2⟩
  smul_mem' := fun t _ hx ↦ ⟨congrArg (t • ·) hx.1, congrArg (t • ·) hx.2⟩

private def boundary (x : Placement E × Placement E) : Placement E :=
  ![x.1 0, x.1 1, x.2 2, x.2 3]

private def boundaryLinear (m : ℝ) (g : Fin 4 → E) :
    (Placement E × Placement E) →ₗ[ℝ] ℝ where
  toFun x := m * (∑ i, ⟪g i, boundary x i⟫_ℝ)
  map_add' x y := by simp [boundary, Fin.sum_univ_four, inner_add_right]; ring
  map_smul' t x := by simp [boundary, Fin.sum_univ_four, real_inner_smul_right]; ring

private theorem exists_scaled_inner_tuple (m : ℝ) (hm : 0 < m) (L : Placement E →ₗ[ℝ] ℝ) :
    ∃ k : Fin 4 → E, ∀ x, L x = m * ∑ i, ⟪k i, x i⟫_ℝ := by
  obtain ⟨g, hg⟩ := exists_inner_tuple L
  refine ⟨fun i ↦ m⁻¹ • g i, fun x ↦ ?_⟩
  simp [hg, real_inner_smul_left, ← Finset.mul_sum, hm.ne']

/-- The force-lifting property for two phases follows from the price bound for
contracting co-located legs and from sublinearity of the constituent prices. -/
theorem lift_two_phase_force {m : ℝ} (hm : 0 < m)
    {T H D : (Fin 4 → E) → ℝ} (hH : SublinearPrice H) (hD : SublinearPrice D)
    (hwire : ∀ A B U V C F, T ![A,B,C,F] ≤ H ![A,B,U,V] + D ![U,V,C,F])
    {g : Fin 4 → E} (hg : IsNormalizedForce m T g) :
    ∃ a b : E, IsNormalizedForce m H ![g 0,g 1,-a,-b] ∧
      IsNormalizedForce m D ![a,b,g 2,g 3] := by
  let L := (boundaryLinear m g).toPMap (glued E)
  let P := fun z : Placement E × Placement E ↦ H z.1 + D z.2
  have hsub : SublinearPrice P := by
    constructor
    · intro t ht x
      exact (congrArg₂ (·+·) (hH.hom t ht x.1) (hD.hom t ht x.2)).trans (mul_add ..).symm
    · intro x y
      dsimp [P]
      linarith [hH.add_le x.1 y.1, hD.add_le x.2 y.2]
  have hdom (z : L.domain) : L z ≤ P z := by
    obtain ⟨⟨u,v⟩, huv⟩ := z
    change u 2 = v 0 ∧ u 3 = v 1 at huv
    change m * (∑ i, ⟪g i, boundary (u,v) i⟫_ℝ) ≤ H u + D v
    have h := (hg _).trans (hwire (u 0) (u 1) (u 2) (u 3) (v 2) (v 3))
    have h₁ : ![u 0,u 1,u 2,u 3] = u := by funext i; fin_cases i <;> rfl
    have h₂ : ![u 2,u 3,v 2,v 3] = v := by
      rw [huv.1, huv.2]; funext i; fin_cases i <;> rfl
    simpa only [boundary, h₁, h₂] using h
  obtain ⟨K, hK, hk⟩ := exists_extension_of_le_sublinear L P
    (fun t ht ↦ hsub.hom t ht.le) hsub.add_le hdom
  obtain ⟨l, hl⟩ := exists_scaled_inner_tuple m hm (K.comp (LinearMap.inl ℝ _ _))
  obtain ⟨s, hs⟩ := exists_scaled_inner_tuple m hm (K.comp (LinearMap.inr ℝ _ _))
  change ∀ x, K (x,0) = _ at hl
  change ∀ x, K (0,x) = _ at hs
  have hlForce : IsNormalizedForce m H l := fun x ↦ by
    simpa only [P, hD.zero, add_zero, hl] using hk (x,0)
  have hsForce : IsNormalizedForce m D s := fun x ↦ by
    simpa only [P, hH.zero, zero_add, hs] using hk (0,x)
  have hid (A B U V C F : E) :
      ⟪l 0,A⟫_ℝ + ⟪l 1,B⟫_ℝ + ⟪l 2,U⟫_ℝ + ⟪l 3,V⟫_ℝ +
      (⟪s 0,U⟫_ℝ + ⟪s 1,V⟫_ℝ + ⟪s 2,C⟫_ℝ + ⟪s 3,F⟫_ℝ) =
      ⟪g 0,A⟫_ℝ + ⟪g 1,B⟫_ℝ + ⟪g 2,C⟫_ℝ + ⟪g 3,F⟫_ℝ := by
    let u := ![A,B,U,V]
    let v := ![U,V,C,F]
    have h := hK ⟨(u,v), ⟨rfl,rfl⟩⟩
    change K (u,v) = m * (∑ i, ⟪g i, boundary (u,v) i⟫_ℝ) at h
    rw [show (u,v) = (u,0) + (0,v) by simp, map_add, hl, hs, ← mul_add] at h
    apply (mul_left_cancel₀ hm.ne')
    simpa [u,v,boundary,Fin.sum_univ_four] using h
  have hl₀ : l 0 = g 0 := ext_inner_right ℝ fun t ↦ by simpa using hid t 0 0 0 0 0
  have hl₁ : l 1 = g 1 := ext_inner_right ℝ fun t ↦ by simpa using hid 0 t 0 0 0 0
  have hs₂ : s 2 = g 2 := ext_inner_right ℝ fun t ↦ by simpa using hid 0 0 0 0 t 0
  have hs₃ : s 3 = g 3 := ext_inner_right ℝ fun t ↦ by simpa using hid 0 0 0 0 0 t
  have hl₂ : l 2 = -s 0 := ext_inner_right ℝ fun t ↦ by
    rw [inner_neg_left]; apply eq_neg_of_add_eq_zero_left; simpa using hid 0 0 t 0 0 0
  have hl₃ : l 3 = -s 1 := ext_inner_right ℝ fun t ↦ by
    rw [inner_neg_left]; apply eq_neg_of_add_eq_zero_left; simpa using hid 0 0 0 t 0 0
  have hleq : l = ![g 0,g 1,-s 0,-s 1] := by
    funext i; fin_cases i <;> assumption
  have hseq : s = ![s 0,s 1,g 2,g 3] := by
    funext i; fin_cases i <;> first | rfl | assumption
  exact ⟨s 0,s 1,hleq ▸ hlForce,hseq ▸ hsForce⟩

end FiniteFourier
end LinearAlgebra
end OAI
