import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Coordinates for the monomial map between the two rectangle endpoints

The change from label-adapted charts to the common paired charts is block
triangular. Its diagonal blocks act invertibly on the summation subspace and
on its quotient. Pulling frequencies back by the dual of the first block
gives the two frequency coordinates needed by the endpoint bridge.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*} [Field K]

private theorem exists_endpoint_chart_blocks {H S P : Type*}
    [AddCommGroup H] [Module K H] [AddCommGroup S] [Module K S] [AddCommGroup P] [Module K P]
    (u : (H × S) ≃ₗ[K] H × P) (hu : ∀ x, (u x).2 = 0 ↔ x.2 = 0) :
    ∃ (a : H ≃ₗ[K] H) (c : S ≃ₗ[K] P),
      (∀ h, u (h, 0) = (a h, 0)) ∧ (∀ s, (u (0, s)).2 = c s) := by
  let f := LinearMap.fst K H P ∘ₗ u.toLinearMap ∘ₗ LinearMap.inl K H S
  let g := LinearMap.snd K H P ∘ₗ u.toLinearMap ∘ₗ LinearMap.inr K H S
  have hfirst (h : H) : u (h, 0) = (f h, 0) :=
    Prod.ext rfl ((hu (h,0)).2 rfl)
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      have h : u (x,0) = u (y,0) := by rw [hfirst, hfirst, he]
      exact congrArg Prod.fst (u.injective h)
    · intro h
      obtain ⟨⟨z,s⟩,hpre⟩ := u.surjective (h,0)
      have : s = 0 := (hu (z,s)).1 (by rw [hpre])
      subst s
      exact ⟨z, congrArg Prod.fst hpre⟩
  have hg : Function.Bijective g := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro s hs
      exact (hu (0,s)).1 hs
    · intro p
      obtain ⟨⟨h,s⟩,hpre⟩ := u.surjective (0,p)
      refine ⟨s, ?_⟩
      change (u (0,s)).2 = p
      have he : u (h,0) + u (0,s) = (0,p) := by simpa [← map_add] using hpre
      simpa [hfirst] using congrArg Prod.snd he
  exact ⟨LinearEquiv.ofBijective f hf, LinearEquiv.ofBijective g hg, hfirst, fun _ => rfl⟩

private theorem exists_endpoint_dot_pullback {I : Type*} [Fintype I] [DecidableEq I]
    (a : (I → K) ≃ₗ[K] (I → K)) :
    ∃ a' : (I → K) ≃ₗ[K] (I → K), ∀ f x, a' f ⬝ᵥ x = f ⬝ᵥ a x := by
  let d := dotProductEquiv K I
  refine ⟨(d.trans a.dualMap).trans d.symm, fun f x => ?_⟩
  change d (d.symm (a.dualMap (d f))) x = _
  rw [d.apply_symm_apply]
  rfl

/-- In label charts aligned with a common subspace and its annihilator, the
pairing splits into two partial Fourier dot products and a residual pairing
depending only on the two chosen representatives. The label summation bases
on the two sides may be chosen independently. -/
theorem exists_endpointBridgeCoordinates {I J E S T : Type*} [Fintype I] [Fintype J]
    [AddCommGroup E] [Module K E] [AddCommGroup S] [Module K S] [AddCommGroup T] [Module K T]
    (B : LinearMap.BilinForm K E)
    (e e' : E ≃ₗ[K] (I → K) × (J → K))
    (A : E ≃ₗ[K] (I → K) × S) (Z : E ≃ₗ[K] (J → K) × T)
    (ha : ∀ x, (A x).2 = 0 ↔ (e x).2 = 0)
    (hz : ∀ y, (Z y).2 = 0 ↔ (e' y).1 = 0)
    (hb : ∀ x y, B x y = (e x).1 ⬝ᵥ (e' y).1 + (e x).2 ⬝ᵥ (e' y).2) :
    ∃ (bS : S ≃ₗ[K] (J → K)) (bT : T ≃ₗ[K] (I → K)), ∀ h s p t,
      B (A.symm (h,s)) (Z.symm (p,t)) = h ⬝ᵥ bT t + bS s ⬝ᵥ p +
        B (A.symm (0,s)) (Z.symm (0,t)) := by
  classical
  let u := A.symm.trans e
  let v := (Z.symm.trans e').trans (LinearEquiv.prodComm K _ _)
  have hu (x) : (u x).2 = 0 ↔ x.2 = 0 := by simpa [u] using (ha (A.symm x)).symm
  have hv (y) : (v y).2 = 0 ↔ y.2 = 0 := by simpa [v] using (hz (Z.symm y)).symm
  obtain ⟨a,c,ha₀,hc⟩ := exists_endpoint_chart_blocks u hu
  obtain ⟨z,d,hz₀,hd⟩ := exists_endpoint_chart_blocks v hv
  obtain ⟨a',ha'⟩ := exists_endpoint_dot_pullback a
  obtain ⟨z',hz'⟩ := exists_endpoint_dot_pullback z
  refine ⟨c.trans z', d.trans a', fun h s p t => ?_⟩
  have hA (h) : e (A.symm (h,0)) = (a h, 0) := ha₀ h
  have hZ (p) : e' (Z.symm (p,0)) = (0, z p) := by
    exact Prod.ext (congrArg Prod.snd (hz₀ p)) (congrArg Prod.fst (hz₀ p))
  calc
    _ = B (A.symm (h,0)) (Z.symm (p,0)) + B (A.symm (h,0)) (Z.symm (0,t)) +
        B (A.symm (0,s)) (Z.symm (p,0)) + B (A.symm (0,s)) (Z.symm (0,t)) := by
          have hhs : (h,s) = (h,0) + (0,s) := by simp
          have hpt : (p,t) = (p,0) + (0,t) := by simp
          rw [hhs, hpt, map_add, map_add, map_add, LinearMap.add_apply]
          simp only [map_add, add_assoc]
    _ = _ := by
      rw [hb (A.symm (h,0)) (Z.symm (p,0)), hb (A.symm (h,0)) (Z.symm (0,t)),
        hb (A.symm (0,s)) (Z.symm (p,0)), hA, hZ]
      have hs : (e (A.symm (0,s))).2 = c s := hc s
      have ht : (e' (Z.symm (0,t))).1 = d t := hd t
      simp only [zero_dotProduct, dotProduct_zero, zero_add, add_zero, LinearEquiv.trans_apply,
        hs, ht, hz']
      rw [dotProduct_comm h, ha', dotProduct_comm (d t)]

end FiniteFourier
end LinearAlgebra
end OAI
