import OAI.Hierarchy.ProbeFixedFormatCore
import OAI.Hierarchy.TaggedWidthProtocol

namespace OAI
/-! # Selecting the physical protocol used by the wide induction -/

noncomputable section
namespace Hierarchy.Tagged
open ProtocolRAM.Calendar

/-- The simultaneous parameter choice selects the original sampler and both
signed catalogues. Their scale, number of attempts and radius are fixed
before the height, payload, external tags and selector are supplied. -/
theorem choose_fixed_format {F : Type*} [Field F] {k : ℕ} (hk : 0<k)
    (missing : ¬HasSpectralFlat F (k+1)) {u : ℝ→ℝ} {r A ε : ℝ}
    (profile : TaggedWidthProfile.Admissible r u) (small : 0<ε) :
    ∃ δ η ξ p q Q σ Λ : ℝ, ∃ f : FixedProtocolFormat F k p q Q σ Λ,
      TaggedShorterBudget.Choice u A (ε/2) p q Q σ Λ δ η ξ ∧ 0<f.W ∧ 0<f.radius := by
  obtain ⟨δ,η,ξ,p,q,Q,σ,Λ,⟨f⟩,price⟩ := TaggedShorterBudget.choose (A:=A) profile
    (half_pos small) (cofinal_formats F k hk missing)
  have wide := (le_max_left 9 (2*k+1)).trans f.geometry.wide
  have radius := f.geometry.large
  exact ⟨δ,η,ξ,p,q,Q,σ,Λ,f,price,by omega,by omega⟩

/-- With the physical records evaluated on each chosen chart, the public
parameter quantifier in the width closure is discharged by the actual
cofinal protocol construction. -/
def fixed_readouts {F : Type*} [Field F] {k : ℕ} (hk : 0<k)
    (missing : ¬HasSpectralFlat F (k+1))
    (chart : ∀ {u : ℝ→ℝ} {κ A ε p q Q σ Λ δ η ξ : ℝ},
      TaggedWidthProfile.Admissible (profile F k 1) u → 0<κ → 1+κ≤A → 0<ε →
      FixedProtocolFormat F k p q Q σ Λ → TaggedShorterBudget.Choice u A (ε/2) p q Q σ Λ δ η ξ →
      Nonempty (ProtocolReadout F k u κ A δ ξ)) : CofinalReadouts F k where
  parameters := fun _ p q Q σ Λ=>Nonempty (FixedProtocolFormat F k p q Q σ Λ)
  protocols := fun _ _=>cofinal_formats F k hk missing
  readout := fun hu hκ hA hε ⟨f⟩ paid=>chart hu hκ hA hε f paid

end Hierarchy.Tagged

end
end OAI
