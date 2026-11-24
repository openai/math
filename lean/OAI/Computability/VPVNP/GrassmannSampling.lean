import OAI.Computability.VPVNP.GrassmannIndependent
import OAI.Computability.VPVNP.GrassmannAdjacentFrame
import OAI.Computability.VPVNP.UniformLinearSampling

/-!
# Conditional sampling on adjacent Grassmannian planes

Section 5.2 of *VP and VNP differ over every field* samples a linear map
on the whole ambient space. On adjacent planes, the joint law of its basis
readings consists of one shared tuple on the intersection and two independent
values on the extension columns. Changes of basis express both endpoints in
the fixed vertex coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

variable {n : ℕ} (E : Type*) [AddCommGroup E] [Module (ZMod 2) E]

private def appendCoordinate :
    ((Fin n → E) × E) ≃ (Fin (n + 1) → E) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ ↦ E))

private noncomputable def readInFixedBasis (U : Plane (n + 1)) (b : Fin n → Space (n + 1))
    (a : Space (n + 1)) (hi : LinearIndependent (ZMod 2) (Fin.snoc b a : Fin (n+1) → _))
    (hs : Submodule.span (ZMod 2) (Set.range (Fin.snoc b a : Fin (n+1) → _)) = U.val) :
    ((Fin n → E) × E) ≃ (Fin (n+1) → E) :=
  let b' := (Module.Basis.span hi).map (LinearEquiv.ofEq _ _ hs)
  ((appendCoordinate E).trans (b'.constr (ZMod 2)).toEquiv).trans
    ((planeBasis U).constr (ZMod 2)).symm.toEquiv

private theorem readInFixedBasis_apply (U : Plane (n + 1)) (b : Fin n → Space (n+1))
    (a : Space (n+1)) (hi : LinearIndependent (ZMod 2) (Fin.snoc b a : Fin (n+1) → _))
    (hs : Submodule.span (ZMod 2) (Set.range (Fin.snoc b a : Fin (n+1) → _)) = U.val)
    (f : Space (n + 1) →ₗ[ZMod 2] E) :
    readInFixedBasis E U b a hi hs (fun i ↦ f (b i), f a) = readPlane E U f := by
  let b' := (Module.Basis.span hi).map (LinearEquiv.ofEq _ _ hs)
  have he : b'.constr (ZMod 2) (appendCoordinate E (fun i ↦ f (b i), f a)) =
      f.comp U.val.subtype := by
    apply b'.ext
    intro j
    rw [Module.Basis.constr_basis]
    change (Fin.snoc (fun i ↦ f (b i)) (f a) : Fin (n+1) → E) j = f ((b' j : U.val) : Space (n+1))
    have hbj : ((b' j : U.val) : Space (n+1)) = (Fin.snoc b a : Fin (n+1) → Space (n+1)) j := by
      simp [b', Module.Basis.map_apply]
    rw [hbj]
    cases j using Fin.lastCases <;> simp
  change ((planeBasis U).constr (ZMod 2)).symm (b'.constr (ZMod 2) _) = _
  rw [he]
  rfl

private def appendTwoCoordinates :
    (((Fin n → E) × E) × E) ≃ (Fin (n + 2) → E) :=
  ((appendCoordinate E).prodCongr (Equiv.refl E)).trans (appendCoordinate E)

private theorem appendTwoCoordinates_eval (b : Fin n → Space (n+1)) (a c : Space (n+1))
    (f : Space (n+1) →ₗ[ZMod 2] E) :
    appendTwoCoordinates E ((fun i ↦ f (b i), f a), f c) =
      fun j ↦ f ((Fin.snoc (Fin.snoc b a) c : Fin (n+2) → Space (n+1)) j) := by
  funext j
  change (Fin.snoc (Fin.snoc (fun i ↦ f (b i)) (f a)) (f c) : Fin (n+2) → E) j =
    f ((Fin.snoc (Fin.snoc b a) c : Fin (n+2) → Space (n+1)) j)
  cases j using Fin.lastCases with
  | last => simp
  | cast j => cases j using Fin.lastCases <;> simp

/-- For any observable of the two endpoints, the mean over all linear maps is
exactly the mean over the two extensions of the common restriction. Both
endpoint charts are independent of the observable. -/
theorem exists_adjacent_charts [Fintype E] (p : Pair (n+1) 1) :
    ∃ l r : ((Fin n → E) × E) ≃ (Fin (n+1) → E), ∀ g : (Fin (n+1) → E) → (Fin (n+1) → E) → ℝ,
      (∑ f : Space (n+1) →ₗ[ZMod 2] E, g (readPlane E p.val.1 f) (readPlane E p.val.2 f)) /
        Fintype.card (Space (n+1) →ₗ[ZMod 2] E) =
      ((∑ i, ∑ a, ∑ c, g (l (i,a)) (r (i,c))) / Fintype.card E) / Fintype.card (Fin (n+1) → E) := by
  obtain ⟨b, u, v, hw, hu, hv, hsu, hsv⟩ := exists_adjacent_frame p
  let l := readInFixedBasis E p.val.1 b u hu hsu
  let r := readInFixedBasis E p.val.2 b v hv hsv
  refine ⟨l, r, ?_⟩
  intro g
  let d (z : ((Fin n → E) × E) × E) := g (l z.1) (r (z.1.1, z.2))
  let e := appendTwoCoordinates (n := n) E
  let w := (Fin.snoc (Fin.snoc b u) v : Fin (n+2) → Space (n+1))
  have hread (f : Space (n+1) →ₗ[ZMod 2] E) :
      d (e.symm (fun j ↦ f (w j))) = g (readPlane E p.val.1 f) (readPlane E p.val.2 f) := by
    have he : e.symm (fun j ↦ f (w j)) = ((fun i ↦ f (b i), f u), f v) :=
      e.symm_apply_eq.mpr (appendTwoCoordinates_eval E b u v f).symm
    simp only [he, d, l, r, readInFixedBasis_apply]
  have hs : (∑ y : Fin (n+2) → E, d (e.symm y)) = ∑ i, ∑ a, ∑ c, g (l (i,a)) (r (i,c)) := by
    rw [← e.sum_comp (fun y ↦ d (e.symm y))]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, d]
  have hcard : (Fintype.card (Fin (n+2) → E) : ℝ) =
      Fintype.card E * (Fintype.card (Fin (n+1) → E) : ℝ) := by
    have hc := Fintype.card_congr (appendCoordinate (n := n+1) E).symm
    rw [Fintype.card_prod, Nat.mul_comm] at hc
    exact_mod_cast hc
  have h := SpectralGeometry.uniformAverage_frame_eval w hw (fun y ↦ d (e.symm y))
  simp only [hread, hs, hcard] at h
  simpa only [div_div] using h

end Grassmann

end VPVNP
end Computability
end OAI
