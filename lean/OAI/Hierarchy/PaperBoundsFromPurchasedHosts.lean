import OAI.Hierarchy.PaperThreeFlatSpectralDescent
import OAI.Hierarchy.DescentSpectralPurchasedHosts
import OAI.Hierarchy.TaggedWideCalendarReduction
import OAI.Hierarchy.GridTraceConstruction

namespace OAI
/-! # All-field bounds from the selected native host on the fixed spectral rotor -/
namespace Hierarchy
open LinearAlgebra.SpectralBooks DescentSixParty
noncomputable section

variable (hosts : ∀(p : ℕ) [Fact p.Prime] (G : PoweredGadget (ZMod p)) (c : EpochRotor G),
  ∃drift limit : ℕ, c.ProducesHosts drift limit)

include hosts

theorem prime_flat_from_purchased_hosts (p d : ℕ) [Fact p.Prime] : HasSpectralFlat (ZMod p) d :=by
  apply prime_flat_of_spectral_descent p _ _ _ d
  · intro k hk _ miss _
    exact Tagged.width_reductions (by omega) miss
  · intro family
    exact descent_of_spectral_hosts family (hosts p)
  · intro k hk family
    exact GridChosenReceiver.native_grid k (by omega) family

theorem unbounded_prime_flats_from_purchased_hosts : UnboundedPrimeFieldFlats :=by
  apply UnboundedPrimeFieldFlats.of_all
  intro p _ d _
  exact prime_flat_from_purchased_hosts hosts p d

theorem paper_bounds_from_purchased_hosts (F : Type*) [Field F] :
    (VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F) ∧
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤formalOmega F 1 1 1 ∧
    (1097:ℝ)/500<formalOmega F 1 1 1 :=by
  exact paper_bounds_of_spectral_flats (unbounded_prime_flats_from_purchased_hosts hosts) F

theorem division_exponent_from_purchased_hosts (F : Type*) [Field F] :
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤divisionOmega F 1 1 1 ∧
    (1097:ℝ)/500<divisionOmega F 1 1 1 :=by
  rw [divisionOmega_square_eq_formalOmega]
  exact (paper_bounds_from_purchased_hosts hosts F).2

/-- The same prime-field construction also gives the earlier three-dimensional
profile bound for the division-free and division models. -/
theorem three_flat_square_from_purchased_hosts (F : Type*) [Field F] :
    let c:=ThreeFlat.omegaThree
    (c≤formalOmega F 1 1 1 ∧ c≤divisionOmega F 1 1 1) ∧
    ((43:ℝ)/20≤formalOmega F 1 1 1 ∧ (43:ℝ)/20≤divisionOmega F 1 1 1) :=by
  have bound:=ThreeFlat.square_exponents_of_prime_threeFlats
    (fun p _ => prime_flat_from_purchased_hosts hosts p 3) F
  have cert:=ThreeFlat.fortyThree_div_twenty_le_omegaThree
  exact ⟨bound,cert.trans bound.1,cert.trans bound.2⟩

end
end Hierarchy

end OAI
