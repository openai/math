import OAI.Computability.NearSquareRoot.FixedCandidateCRTKernelCases
import OAI.Computability.NearSquareRoot.FixedCandidateCRTHalfStage

/-! # Linear-space CRT and inverse CRT on arbitrary padded records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code Space DigitPacking FixedPoint Filter CRTDispatch Controlled

noncomputable section

private theorem direction {ρ : ℝ} (hρ : 1/2 < ρ) (h₁ : ρ ≤ 1) (inv : Bool) :
    ∃ K : ℕ, ∀ {I : Type} (n : I → ℕ) (valid : ∀ i, Directory (n i)),
      (∀ i, 2 ≤ n i) → (∀ i, K ≤ addressBits (n i)) →
      StreamPass n (CRTBudget.routeClock ρ 0) (fun i => outcome (valid i) inv) := by
  obtain ⟨K₁,hK₁⟩ := Site.run hρ h₁ inv
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp CRTBudget.eventually_capacity_pos
  obtain ⟨K₃,hK₃⟩ := eventually_atTop.mp
    (CRTBudget.eventually_fixedLow_native_admission 0 1 (by linarith : 0 ≤ ρ) h₁)
  refine ⟨max K₁ (max K₂ K₃),fun n valid hn hk => ?_⟩
  have lim₁ i : K₁ ≤ addressBits (n i) := (le_max_left ..).trans (hk i)
  have lim₂ i : K₂ ≤ addressBits (n i) := (le_max_left ..).trans ((le_max_right ..).trans (hk i))
  have lim₃ i : K₃ ≤ addressBits (n i) := (le_max_right ..).trans ((le_max_right ..).trans (hk i))
  have cap i : 0 < Cap (addressBits (n i)) := hK₂ _ (lim₂ i)
  let Y := Half.KernelIndex n inv
  let build (z : Y) : Site ρ inv :=
    { n := n z.1.1, valid := valid z.1.1, stage := z.1.2.1.val,
      generated := z.1.2.1.property, β := z.2.1
      admit := hK₃ _ (lim₃ z.1.1) _
        (selected_count (cap z.1.1) _ _ _) (by simp)
      values := Benes.scatter z.2.2 (pack (valid z.1.1) z.1.2.1.val z.1.2.2) }
  have pass := hK₁ build (fun z => lim₁ z.1.1)
  exact Half.nativeSweep n valid inv hn cap ρ 0
    (pass.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

/-- Both physical CRT gates for a fixed exponent. The same cutoff admits every
original data size and all padding records. Each gate has a single finite command,
linear peak space in input bits, and the charged physical logarithmic clock. -/
theorem largePasses {ρ : ℝ} (hρ : 1/2 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ K deg : ℕ, ∀ {I : Type} (n : I → ℕ) (valid : ∀ i, Directory (n i)),
      (∀ i, 2 ≤ n i) → (∀ i, K ≤ addressBits (n i)) → ∀ inv : Bool,
      StreamPass n (CRTBudget.routeClock ρ deg) (fun i => outcome (valid i) inv) := by
  obtain ⟨F,forward⟩ := direction hρ hρ₁ false
  obtain ⟨B,backward⟩ := direction hρ hρ₁ true
  refine ⟨max F B,0,fun n valid hn hk inv => ?_⟩
  cases inv
  · exact forward n valid hn (fun i => (le_max_left ..).trans (hk i))
  · exact backward n valid hn (fun i => (le_max_right ..).trans (hk i))

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
