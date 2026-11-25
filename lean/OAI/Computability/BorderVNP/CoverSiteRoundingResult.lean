import OAI.Computability.BorderVNP.CoverSiteRoundingSelection
import OAI.Computability.BorderVNP.CoverSiteRoundingLoads

/-!
# The final site-rounding estimates of Lemma 6.1

The last motion is fixed globally for the pack. Its positive nonlocal width
is the width of segments whose endpoints go to distinct sites. Each such
width contributes at both sites to the incidence histogram. The two bounds
below use exactly the same motion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Finset UpperHalfPlane BorderVNP.Cover.Frame

private theorem center_return : toBaseTile I = 1 := by
  let u := toBaseTile I
  have h := (toBaseTile_mem I).1 u
  have he : gammaSL 1 u • I = I := dist_le_zero.mp (by change dist (gammaSL 1 u • I) I ≤ dist (gammaSL 1 u • I) (gammaSL 1 u • I) at h; rwa [dist_self] at h)
  exact eq_one_of_fix u I he

/-- The site's own deck address is precisely the label used to define it. -/
theorem surfaceAddress_site (d : ℕ) (t : Deck (d+1)) : surfaceAddress d (deckSite d t) = t := by
  induction t using QuotientGroup.induction_on with
  | _ b =>
    change (((toBaseTile (gammaSL 1 b • I))⁻¹ : gamma 1) : Deck (d+1)) = _
    rw [toBaseTile_smul,center_return,one_mul,inv_inv]

/-- Rounding does not change the tile address. -/
theorem surfaceAddress_roundedSite (d : ℕ) (x : Surface (d+1)) :
    surfaceAddress d (roundedSite d x) = surfaceAddress d x := surfaceAddress_site d _

private theorem productRoundingFailure_mem {q : ℕ} (d : ℕ) (x y : Fin q → Surface (d+1)) :
    0 ≤ productRoundingFailure d x y ∧ productRoundingFailure d x y ≤ 1 := by
  classical
  unfold productRoundingFailure
  split_ifs <;> norm_num

/-- Joint site rounding bounds the nonlocal bits and the concentration of their two
endpoint incidences simultaneously. The first constant is independent of the length
list, the cover level, the motion denominator, and the network. -/
theorem site_rounding_bounds : ∃ C ≥ (0:ℝ), ∀ {L : Type} [Fintype L] (r : L → ℝ),
    (∀ l, 0 ≤ r l) → (∀ l, 4*r l ≤ 1) →
    ∃ (a m : ℕ) (u : Fin m → SL) (hu : ∀ i, Clears (u i) a),
    ∀ (q : ℕ) (ρ : ℝ), ∃ N : ℕ, ∀ d {W : Type*} [Fintype W] (ℓ : W → L) (w : W → ℝ),
      (∀ j, 0 ≤ w j) →
      ∀ (c : W → Fin q → Surface (d+2+2*a)) (p : W × Bool → Fin q → Surface (d+2+2*a)),
      (∀ j k, dist (p (j,false) k) (p (j,true) k) ≤ r (ℓ j)) →
      (∀ b k, dist (c b.1 k) (p b k) ≤ ρ) →
      ∃ σ : Fin q → Fin m,
      let out (b : W × Bool) (k : Fin q) := surfaceMotion (hu (σ k)) (d+2) (p b k)
      let keep (j : W) := w j * productRoundingFailure (d+1) (out (j,false)) (out (j,true))
      let centers (j : W) (k : Fin q) := addressAt (d+2+2*a) (by omega) (c j k)
      let ends (b : W × Bool) (k : Fin q) := surfaceAddress (d+1) (roundedSite (d+1) (out b k))
      (∑ j, keep j) ≤ q*C * ∑ j, w j * r (ℓ j) ∧
        tileConcentration (tileMass ends (fun b => keep b.1)) ≤
          2*N * tileConcentration (tileMass centers w) := by
  classical
  obtain ⟨C,hC,choice⟩ := exists_rounding_choice
  refine ⟨C,hC,?_⟩
  intro L _ r hnon hsmall
  obtain ⟨a,m,u,hu,hs⟩ := choice r hnon hsmall
  refine ⟨a,m,u,hu,?_⟩
  intro q ρ
  obtain ⟨N,hload⟩ := rounding_load_bounds ρ a q
  refine ⟨N,?_⟩
  intro d W _ ℓ w hw c p hd hr
  obtain ⟨σ,hσ⟩ := hs q (d+1) ℓ w hw (fun j => p (j,false)) (fun j => p (j,true)) hd
  refine ⟨σ,?_⟩
  intro out keep centers ends
  have hkeep (b : W × Bool) : 0 ≤ keep b.1 ∧ keep b.1 ≤ w b.1 := by
    have h := productRoundingFailure_mem (d+1) (out (b.1,false)) (out (b.1,true))
    exact ⟨mul_nonneg (hw _) h.1, (mul_le_mul_of_nonneg_left h.2 (hw _)).trans_eq (mul_one _)⟩
  have hl := (hload d (fun k => u (σ k)) (fun k => hu (σ k)) w (fun b => keep b.1) hw hkeep c p hr).2
  have he : ends = fun b k => surfaceAddress (d+1) (out b k) :=
    funext fun b => funext fun k => surfaceAddress_roundedSite (d+1) (out b k)
  rw [he]
  exact ⟨hσ,by simpa [centers,out,mul_comm (2:ℝ)] using hl⟩

end Cover

end BorderVNP
end Computability
end OAI
