import OAI.Computability.BorderVNP.PackedFrozenNamedCarry
import OAI.Computability.BorderVNP.PackedFrozenSelectedMeasures

/-! # Uniform cost of the literal carried-tape circuit of a selected round -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch Shortening Shortening.PublicCapacity Diagonal Filter TeamScales
open PackedHistoryCircuit PackedHistoryCircuit.Normalized.SelectedSchedule VPVNP.VerifierNetwork
open CellPacketGeometry.LiveWords
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- At every selected subround the actual finite schema's row count pays
for the literal fixed carry circuit used by the named saved-directory proof.
The one coefficient is chosen before the input, parallelism and base format. -/
theorem eventually_stage_carry {a x : ℕ} (s : EpochScales S a x) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      let w := 60*logWidth r n
      ∀ base : Format, Fintype.card base.Rows ≤ C₀*physicalRows (bottom (D := D) start) →
      S.floor+1+S.drop*(epochs s.τ n) ≤ start →
      ∀ t < epochs s.τ n, ∀ j : Fin S.rounds,
        let shape := before S start t j
        let fmt := stage S start w base t j
        ∀ {σ : Type*} [Fintype σ] (oldRoom : shape.sites ≤ 2^w) (newRoom : S.fanIn*shape.sites ≤ 2^w)
          (childPin : Fin S.fanIn × Pins fmt.Rows fmt.Payload w → σ),
          (carryFrame oldRoom newRoom childPin).size ≤ rowWork C V (logWidth r n) 4 (shape.parallel S.fanIn) := by
  obtain ⟨C,hC⟩ := eventually_carry_cost S s C₀
  refine ⟨C,?_⟩
  filter_upwards [hC] with n budget
  intro r hr start V w base small deep t ht j shape fmt σ inst oldRoom newRoom childPin
  apply (carryFrame_size oldRoom newRoom childPin).trans
  apply budget r hr (Fintype.card base.Rows) small t ht j
  exact (stage_slots S start w base deep ht j j.isLt.le).le

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
