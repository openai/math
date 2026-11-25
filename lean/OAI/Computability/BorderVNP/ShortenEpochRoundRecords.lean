import OAI.Computability.BorderVNP.CoverLorentzProduct
import OAI.Computability.BorderVNP.CoverSiteRoundingResult
import OAI.Computability.BorderVNP.ShortenEpochLocalRecords

/-!
# Retained public and expanded records at the final site motion

Every old descriptor is tested at the moved location of its own incident site.
This treats both ends of a long uncharged cable separately. The motion has
boundedly many input tiles per output tile, and rounding preserves that tile
name.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open BorderVNP.Crossing BorderVNP.Shortening BorderVNP.Cover BorderVNP.Cover.Frame Finset
open scoped Classical

private theorem width_test_mono {E : Type*} [Fintype E] (f : E → ℕ) {s t : E → Prop}
    (h : ∀ x, s x → t x) : testedWidth f s ≤ testedWidth f t := by
  unfold testedWidth
  apply sum_le_sum
  intro x _
  by_cases hs : s x
  · simp [hs,h x hs]
  · simp [hs]

private theorem localRecords_mono {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (ex : Bool) (prior payload : N.Site → ℕ) {s t : N.Site → Prop}
    (h : ∀ v, s v → t v) : localRecords N ex prior payload s ≤ localRecords N ex prior payload t := by
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (width_test_mono _ h)
    (width_test_mono _ (fun e => h (N.src e)))) (width_test_mono _ (fun e => h (N.dst e))))
      (width_test_mono _ (fun p => h (N.attach p)))

/-- One uniform per-tile record factor works for every candidate final motion, for both
public and expanded data, and includes all original boxes, ports, ends and histories. -/
theorem final_round_record_bounds (a : ℕ) (I : Type) [Fintype I] : ∃ C : ℕ, ∀ d (g : I → SL) (hg : ∀ i, Clears (g i) a)
    {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (x : N.Site → SurfaceHost I (d+2+2*a)) (prior payload : N.Site → ℕ) (ex : Bool)
    (M : ℕ), (∀ s, localRecords N ex prior payload (fun v =>
        (fun k => addressAt (d+2+2*a) (by omega) (x v k)) = s) ≤ M) →
    ∀ t, localRecords N ex prior payload (fun v =>
        (fun k => surfaceAddress (d+1) (roundedSite (d+1) (surfaceMotion (hg k) (d+2) (x v k)))) = t) ≤ C*M := by
  classical
  obtain ⟨C,hC⟩ := finite_product_motion_neighbors 0 a I
  refine ⟨C,?_⟩
  intro d g hg D P _ bits N x prior payload ex M hm t
  obtain ⟨sources,hin,_,hmem⟩ := hC d g hg
  let src (v : N.Site) (k : I) := addressAt (d+2+2*a) (by omega) (x v k)
  let dest (v : N.Site) (k : I) := surfaceAddress (d+1) (surfaceMotion (hg k) (d+2) (x v k))
  have he (v : N.Site) : src v ∈ sources (dest v) := hmem (fun k => x v k) (fun k => x v k) (by simp)
  simp only [surfaceAddress_roundedSite]
  change localRecords N ex prior payload (fun v => dest v = t) ≤ C*M
  calc
    _ ≤ localRecords N ex prior payload (fun v => src v ∈ sources t) :=
      localRecords_mono (s := fun v => dest v = t) (t := fun v => src v ∈ sources t)
        _ _ _ _ (fun v hv => hv ▸ he v)
    _ = _ := localRecords_near _ _ _ _ src (sources t)
    _ ≤ ∑ _s ∈ sources t, M := sum_le_sum (fun s _ => hm s)
    _ ≤ C*M := by simpa using Nat.mul_le_mul_right M (hin t)

end Epoch

end BorderVNP
end Computability
end OAI
