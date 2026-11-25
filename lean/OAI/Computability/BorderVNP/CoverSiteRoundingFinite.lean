import OAI.Computability.BorderVNP.CoverSiteRoundingResult

/-!
# Final rounding on any finite product of congruence surfaces

The frame motion table and tile loads are invariant under renaming the
coordinate set. This allows the same table to be used directly on a host
whose factors are indexed by the sign vectors of the crossing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Finset BorderVNP.Cover.Frame
open scoped Classical

/-- The bit recorded if the two endpoints round to distinct product sites. -/
noncomputable def coordinateRoundingFailure {I : Type*} (d : ℕ) (x y : I → Surface (d+1)) : ℝ :=
  if (fun i => roundedSite d (x i)) = (fun i => roundedSite d (y i)) then 0 else 1

private theorem rounding_reindex {I : Type*} {q : ℕ} (e : I ≃ Fin q) (d : ℕ) (x y : I → Surface (d+1)) :
    productRoundingFailure d (x ∘ e.symm) (y ∘ e.symm) = coordinateRoundingFailure d x y := by
  have he : (fun i => roundedSite d (x (e.symm i))) = (fun i => roundedSite d (y (e.symm i))) ↔
      (fun i => roundedSite d (x i)) = (fun i => roundedSite d (y i)) := by
    constructor
    · intro h; exact funext fun i => by simpa using congrFun h (e i)
    · intro h; exact funext fun i => congrFun h (e.symm i)
  simp only [productRoundingFailure,coordinateRoundingFailure,Function.comp_apply,he]

private theorem tileConcentration_reindex {E T U : Type*} [Fintype E] [Fintype T] [Fintype U]
    [DecidableEq T] [DecidableEq U] (e : T ≃ U) (loc : E → T) (w : E → ℝ) :
    tileConcentration (tileMass (e ∘ loc) w) = tileConcentration (tileMass loc w) := by
  have h (t) : tileMass (e ∘ loc) w (e t) = tileMass loc w t := by simp [tileMass]
  unfold tileConcentration Epoch.binEnergy
  rw [Fintype.card_congr e,← e.sum_comp (fun u => (tileMass (e ∘ loc) w u)^2)]
  simp only [h]

/-- A single finite Hecke table controls total rounded width and both endpoint
loads on every finite product, with the same constants on every level. -/
theorem finite_site_rounding_bounds : ∃ C ≥ (0:ℝ), ∀ {L : Type} [Fintype L] (r : L → ℝ),
    (∀ l, 0 ≤ r l) → (∀ l, 4*r l ≤ 1) →
    ∃ (a m : ℕ) (u : Fin m → SL) (hu : ∀ i, Clears (u i) a),
    ∀ (I : Type*) [Fintype I] (ρ : ℝ), ∃ N : ℕ, ∀ d {W : Type*} [Fintype W] (ℓ : W → L) (w : W → ℝ),
      (∀ j, 0 ≤ w j) →
      ∀ (c : W → I → Surface (d+2+2*a)) (p : W × Bool → I → Surface (d+2+2*a)),
      (∀ j k, dist (p (j,false) k) (p (j,true) k) ≤ r (ℓ j)) →
      (∀ b k, dist (c b.1 k) (p b k) ≤ ρ) →
      ∃ σ : I → Fin m,
      let out (b : W × Bool) (k : I) := surfaceMotion (hu (σ k)) (d+2) (p b k)
      let keep (j : W) := w j * coordinateRoundingFailure (d+1) (out (j,false)) (out (j,true))
      let centers (j : W) (k : I) := addressAt (d+2+2*a) (by omega) (c j k)
      let ends (b : W × Bool) (k : I) := surfaceAddress (d+1) (roundedSite (d+1) (out b k))
      (∑ j, keep j) ≤ Fintype.card I*C * ∑ j, w j * r (ℓ j) ∧
        tileConcentration (tileMass ends (fun b => keep b.1)) ≤
          2*N * tileConcentration (tileMass centers w) := by
  obtain ⟨C,hC,choose⟩ := site_rounding_bounds
  refine ⟨C,hC,?_⟩
  intro L _ r hr hsmall
  obtain ⟨a,m,u,hu,h⟩ := choose r hr hsmall
  refine ⟨a,m,u,hu,?_⟩
  intro I _ ρ
  let e := Fintype.equivFin I
  obtain ⟨N,hN⟩ := h (Fintype.card I) ρ
  refine ⟨N,?_⟩
  intro d W _ ℓ w hw c p hd hc
  obtain ⟨σ,hσ⟩ := hN d ℓ w hw (fun j => c j ∘ e.symm) (fun b => p b ∘ e.symm)
    (fun j k => hd j (e.symm k)) (fun b k => hc b (e.symm k))
  refine ⟨σ ∘ e,?_⟩
  intro out keep centers ends
  let key (l : ℕ) := e.arrowCongr (Equiv.refl (Deck l))
  have moved (b : W × Bool) (k : Fin (Fintype.card I)) :
      surfaceMotion (hu (σ k)) (d+2) (p b (e.symm k)) = out b (e.symm k) := by
    simp [out]
  have hk (j : W) : w j * productRoundingFailure (d+1)
      (fun k => surfaceMotion (hu (σ k)) (d+2) (p (j,false) (e.symm k)))
      (fun k => surfaceMotion (hu (σ k)) (d+2) (p (j,true) (e.symm k))) = keep j := by
    simp_rw [moved]; exact congrArg (w j * ·) (rounding_reindex e (d+1) (out (j,false)) (out (j,true)))
  dsimp only [Function.comp_apply] at hσ
  simp_rw [hk] at hσ
  refine ⟨hσ.1,?_⟩
  have hl := hσ.2
  simp_rw [moved] at hl
  change tileConcentration (tileMass (key (d+2) ∘ ends) (fun b => keep b.1)) ≤
    2*N * tileConcentration (tileMass (key (d+2+2*a) ∘ centers) w) at hl
  simpa only [tileConcentration_reindex] using hl

end Cover

end BorderVNP
end Computability
end OAI
