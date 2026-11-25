import OAI.Computability.BorderVNP.ShortenEpochMotionEnergy
import OAI.Computability.BorderVNP.ShortenEpochRoundCatalog

/-!
# Terminal incidence for every candidate motion

Both ends of a charged cable read the same retained mass. This estimate
applies to the candidate selected by minimizing nonlocal integer width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Round

open Cover Cover.Frame Shortening Finset
open scoped Classical

/-- Every cleared motion on the finite product satisfies the endpoint load bound,
including when the retained weights are chosen by testing the moved addresses. -/
theorem all_motion_loads (I : Type) [Fintype I] (ρ : ℝ) (a : ℕ) :
    ∃ N : ℕ, ∀ d (g : I → SL) (hg : ∀ i, Clears (g i) a)
      {W : Type} [Fintype W] (center : W → I → Surface (d+2+2*a))
      (ends : W × Bool → I → Surface (d+2+2*a)) (width keep : W → ℝ),
      (∀ j, 0 ≤ width j) → (∀ j, 0 ≤ keep j ∧ keep j ≤ width j) →
      (∀ b k, dist (center b.1 k) (ends b k) ≤ ρ) →
      let before (j : W) (i : I) := addressAt (d+2+2*a) (by omega) (center j i)
      let after (b : W × Bool) (i : I) := surfaceAddress (d+1) (surfaceMotion (hg i) (d+2) (ends b i))
      tileConcentration (tileMass after (fun b => keep b.1)) ≤
        2*N * tileConcentration (tileMass before width) := by
  classical
  let ι := (Fintype.equivFin I).symm
  obtain ⟨N,hN⟩ := rounding_load_bounds ρ a (Fintype.card I)
  refine ⟨N,?_⟩
  intro d g hg W _ center ends width keep hw hk hd before after
  let inp := ι.symm.arrowCongr (Equiv.refl (Deck (d+2+2*a)))
  let out := ι.symm.arrowCongr (Equiv.refl (Deck (d+2)))
  have H := (hN d (fun k => g (ι k)) (fun k => hg (ι k)) width (fun z : W × Bool => keep z.1)
    hw (fun z => hk z.1) (fun j k => center j (ι k)) (fun j k => ends j (ι k))
    (fun b k => hd b (ι k))).2
  change tileConcentration (tileMass (fun j => out (after j)) (fun b => keep b.1)) ≤
    N*Fintype.card Bool * tileConcentration (tileMass (fun j => inp (before j)) width) at H
  rw [Framed.relabel_tile_concentration out after,Framed.relabel_tile_concentration inp before] at H
  simpa only [Fintype.card_bool,Nat.cast_ofNat,mul_comm (N:ℝ) 2] using H

end Epoch.Round

end BorderVNP
end Computability
end OAI
