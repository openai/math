import OAI.Hierarchy.PaperBoundsAfterRadix

namespace OAI
/-! # Oracle descent is needed only on a prime possessing the missing-flat expander family -/
namespace Hierarchy
open LinearAlgebra.SpectralBooks ThreeFlat Filter
noncomputable section
open scoped Classical

/-- Work on the single prime at which a missing flat is assumed. The spectral
family from this very missing flat supplies both the fixed descent rotor and the grid. -/
theorem prime_flat_of_spectral_descent (p : ℕ) [Fact p.Prime]
    (width : ∀k : ℕ, 2≤k → HasSpectralFlat (ZMod p) k → ¬HasSpectralFlat (ZMod p) (k+1) →
      NonlinearExpanders.SpectralFamily (ZMod p) → Tagged.WidthReductions (ZMod p) k)
    (descent : NonlinearExpanders.SpectralFamily (ZMod p) → CollapseOracle.Descent (ZMod p))
    (compiler : ∀k : ℕ, 2≤k → NonlinearExpanders.SpectralFamily (ZMod p) → GridTraceCompiler (ZMod p) k)
    (d : ℕ) : HasSpectralFlat (ZMod p) d :=by
  by_contra missing
  obtain ⟨k,hk,_,hflat,hmax⟩ := HasSpectralFlat.maximal_of_missing missing
  have miss : ¬ HasSpectralFlat (ZMod p) (k+1) := fun next => Nat.not_succ_le_self _ (hmax _ next)
  have exp := NonlinearExpanders.family_of_missing NonlinearExpanders.excluded_cube (by omega : 2≤k+1) miss
  have reduce := width k hk hflat miss exp
  have radix : Tagged.RadixBound (ZMod p) k := Tagged.Radix.packing_bound
  have Z := Tagged.profile_zero_of_reductions radix reduce
  have cheap (r : ℝ) (hr : 0<r) : Tagged.Feasible (ZMod p) k 1 r :=
    Tagged.feasible_of_profile_lt (Tagged.Exact.rates_nonempty _ _ 1) (by simpa only [Z] using hr)
  have small : Catalyst.HasPointwiseCollapse (ZMod p) k := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    exact CollapseOracle.pointwise_collapse m (descent exp) cheap
  let : NeZero k := ⟨by omega⟩
  obtain ⟨c,run⟩ := compiler k hk exp
  obtain ⟨A,hA,Q,D,env,chosen⟩ := choose_tick small c
  have h := (run A hA Q D env).and_eventually (chosen.and
    (TickSelection.impossible (A:=A) env (by omega : 0<k) hflat.some))
  obtain ⟨w,distribute,⟨v⟩,forbidden⟩ := h.exists
  exact forbidden v (distribute v)


variable (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
    ¬HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
      Tagged.WidthReductions (ZMod p) k)
  (descent : ∀(p : ℕ) [Fact p.Prime], NonlinearExpanders.SpectralFamily (ZMod p) → CollapseOracle.Descent (ZMod p))
  (grid : ∀(p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → NonlinearExpanders.SpectralFamily (ZMod p) →
    GridTraceCompiler (ZMod p) k)

include width descent grid

theorem paper_bounds_of_spectral_descent (F : Type*) [Field F] :
    (VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F) ∧
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤formalOmega F 1 1 1 ∧
    (1097:ℝ)/500<formalOmega F 1 1 1 :=by
  apply paper_bounds_of_spectral_flats _ F
  apply UnboundedPrimeFieldFlats.of_all
  intro p _ d _
  exact prime_flat_of_spectral_descent p (width p) (descent p) (grid p) d

theorem division_exponent_of_spectral_descent (F : Type*) [Field F] :
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤divisionOmega F 1 1 1 ∧
    (1097:ℝ)/500<divisionOmega F 1 1 1 :=by
  rw [divisionOmega_square_eq_formalOmega]
  exact (paper_bounds_of_spectral_descent width descent grid F).2

end
end Hierarchy

end OAI
