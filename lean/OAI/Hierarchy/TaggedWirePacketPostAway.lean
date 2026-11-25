import OAI.Hierarchy.TaggedWireRoutedPackets

namespace OAI
/-! # Routed packet output states at an unvisited site -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Tagged AdaptiveProbe Probe
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators

variable {S H N copies : ℕ} {F : Type} [Field F] {row : Row F S H copies} {phys : Fin N → Chord S}
    (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)

/-- If every positive-width role avoids a site, every physical port there has
zero installed width, so its state has exactly one possible value. -/
theorem post_off_site
    (away : ∀ r, 0 < R.bits c r → ∀ e ∈ R.install.route r, (phys e).1.1 ≠ s ∧ (phys e).1.2 ≠ s) :
    Subsingleton (State (R.post c) s) := by
  have vacant (p : (portGraph S).Port s) : R.post c p.1.1 = 0 := by
    simp only [post, installedWidths, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro e _
    by_cases same : phys e = p.1.1
    · have zero : R.install.load (R.bits c) e = 0 := by
        unfold Installs.load
        apply Finset.sum_eq_zero
        intro r _
        by_cases live : 0 < R.bits c r
        · have absent : e ∉ R.install.route r := by
            intro mem
            have clear := away r live e mem
            rw [same] at clear
            have atSite := p.property
            cases side : p.1.2 <;> rw [side] at atSite
            · first | exact clear.1 atSite
            · first | exact clear.1 atSite | exact clear.2 atSite
          simp [List.count_eq_zero.mpr absent]
        · simp [Nat.eq_zero_of_not_pos live]
      simp [zero]
    · simp [unitChord, same]
  constructor
  intro x y
  funext p
  have singleton (v : Index (R.post c) p.1.1) : v.val = 0 := by
    have bound := v.isLt
    change v.val < 2 ^ (R.post c p.1.1) at bound
    simpa [vacant p] using bound
  exact Fin.ext ((singleton _).trans (singleton _).symm)

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
