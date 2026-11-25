import OAI.Computability.BorderVNP.ShortenEpochNeighbors
import OAI.Computability.BorderVNP.CoverSiteRoundingLoads
import OAI.Computability.BorderVNP.ShortenFramedPacks

/-!
# Concentration of physical wire midpoints under one sampled pack motion

The move acts on the entire set of midpoints. Its tile fibers are uniformly
bounded by the covering degree and local path lifting. The simultaneous
factor permutation and deck posttranslation are included in the estimate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Framed

open Cover Cover.Frame Epoch Hecke Finset
open scoped Classical

variable {I E : Type} [Fintype I] [Fintype E]

/-- Moving a distribution of records across a bijective renaming of tiles
preserves its concentration exactly. -/
theorem relabel_tile_concentration {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (e : S ≃ T) (a : E → S) (w : E → ℝ) :
    tileConcentration (tileMass (fun i => e (a i)) w) = tileConcentration (tileMass a w) := by
  classical
  have he (s : S) : tileMass (fun i => e (a i)) w (e s) = tileMass a w s := by simp [tileMass]
  unfold tileConcentration binEnergy
  rw [← Fintype.card_congr e, ← e.sum_comp (fun t => (tileMass (fun i => e (a i)) w t)^2)]
  simp_rw [he]

set_option maxHeartbeats 1200000 in
/-- Midpoint tile concentration of any single sampled motion, including its
component permutation and integral deck shifts. The multiplier depends on
the word depth and dimension, uniformly over all cover levels and inputs. -/
theorem sampleMove_nearby_tile_concentration (ρ : ℝ) (n : ℕ) :
    ∃ N : ℕ, ∀ d (s : PackSample (lattice 1) elliptic I (d+2) n)
      {E : Type} [Fintype E] (measured mid : E → SurfaceHost I (d+2+2*n)) (w : E → ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, dist (measured i) (mid i) ≤ ρ) →
      tileConcentration (tileMass (fun i => productTileName (d+1) (sampleMove s (mid i))) w) ≤
        (N : ℝ) * tileConcentration (tileMass (fun i k => addressAt (d+2+2*n) (by omega) (measured i k)) w) := by
  classical
  obtain ⟨N,hN⟩ := rounding_load_bounds ρ n (Fintype.card I)
  refine ⟨N,?_⟩
  intro d s E _ measured mid w hw hdist
  let ι := (Fintype.equivFin I).symm
  let j := ι.trans s.1
  let before (i : E) (k : I) := addressAt (d+2+2*n) (by omega) (measured i k)
  let after (i : E) := productTileName (d+1) (sampleMove s (mid i))
  let center (i : E) (k : Fin (Fintype.card I)) := measured i (j k)
  let out := ι.symm.arrowCongr (Equiv.refl (Deck (d+2)))
  let inp := j.symm.arrowCongr (Equiv.refl (Deck (d+2+2*n)))
  let g (k : Fin (Fintype.card I)) := gammaSL 1 (s.2.2 (ι k)).out * wordMatrix s.2.1 (ι k)
  have hg (k) : Clears (g k) n := sample_clears s (ι k)
  have H := (hN d g hg w (fun z : E × Unit => w z.1) hw (fun z => ⟨hw z.1,le_rfl⟩)
    center (fun z k => mid z.1 (j k)) (fun z k => (PiLp.dist_apply_le _ _ (j k)).trans (hdist z.1))).2
  have H' : tileConcentration (tileMass (fun z : E × Unit => out (after z.1)) (fun z => w z.1)) ≤
      (N:ℝ) * Fintype.card Unit * tileConcentration (tileMass (fun i => inp (before i)) w) := H
  have hunit : tileMass (fun z : E × Unit => out (after z.1)) (fun z => w z.1) = tileMass (fun i => out (after i)) w := by
    funext t
    simp [tileMass,Fintype.sum_prod_type]
  rw [hunit] at H'
  calc
    _ = tileConcentration (tileMass (fun i => out (after i)) w) := (relabel_tile_concentration out after w).symm
    _ ≤ (N:ℝ) * Fintype.card Unit * tileConcentration (tileMass (fun i => inp (before i)) w) := H'
    _ = (N:ℝ) * tileConcentration (tileMass before w) := by
      simp only [Fintype.card_unique,Nat.cast_one,mul_one]
      exact congrArg ((N:ℝ) * ·) (relabel_tile_concentration inp before w)

/-- In particular this controls the concentration of the very same chosen
source midpoint before and after its pack motion. -/
theorem sampleMove_tile_concentration (n : ℕ) :
    ∃ N : ℕ, ∀ d (s : PackSample (lattice 1) elliptic I (d+2) n)
      {E : Type} [Fintype E] (mid : E → SurfaceHost I (d+2+2*n)) (w : E → ℝ), (∀ i, 0 ≤ w i) →
      tileConcentration (tileMass (fun i => productTileName (d+1) (sampleMove s (mid i))) w) ≤
        (N : ℝ) * tileConcentration (tileMass (fun i k => addressAt (d+2+2*n) (by omega) (mid i k)) w) := by
  obtain ⟨N,hN⟩ := sampleMove_nearby_tile_concentration (I := I) 0 n
  exact ⟨N,fun d s _ _ mid w hw => hN d s mid mid w hw (fun i => by simp)⟩

end Shortening.Framed

end BorderVNP
end Computability
end OAI
