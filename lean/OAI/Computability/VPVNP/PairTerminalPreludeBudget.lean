import OAI.Computability.VPVNP.PairTerminalPackedBudget
import OAI.Computability.VPVNP.PairTerminalVertexPackedThreshold
import OAI.Computability.VPVNP.PairTraversalControllerSelectedRun

/-!
# Uniform numerical conditions of the packed terminal prefix

The actual live processor clock, the selected block layout and the two
compressor exponents supply every numerical cut used in the bootstrap,
width, traversal, and shared-bit stages. The threshold precedes the selected
level directories, the worker data and the assignments to their coefficients.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLayout

open BurstRAM Compression CursorBounds CursorNetwork CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles Filter

set_option exponentiation.threshold 10000 in
/-- Room for the selected prelude and its closing dispatches on the actual
nested live pair clock. No clock or memory cut is assumed of the workers. -/
theorem eventually_preludeRoom {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {start : ℕ → ℕ} (hstart : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let w := wordBits b n
      let r := addressBits b n
      let T := blockCount (u.θ : ℝ) n
      let X := pairInput S labels hD
      let E := B.execute f hf T hT X
      let L := BlockProgram.layout B (start n) X.positions T
      ∀ (z : E.Choices) (G : LiveProgram.PairStages.Group), n^10000 ≤ G.clock →
        let Y := E.finalState z
        let ls := selectedLayers B f hf T hT X z
        let tags := selected B f hf T hT X z
        let cap := LiveProgram.CompressedPair.clockAt
          (LiveProgram.PairStages.Group.CompressedPaths.publicWords G)
          (LiveProgram.PairStages.Group.CompressedPaths.fuel G)
          LiveProgram.CompressedPair.Stage.terminal
        r < w ∧ 32 ≤ L.base + 2^r*2^r ∧ L.base + 2^r*2^r ≤ 2^w ∧
          endAddress L + 2*words B.recordLimit ls + Y.totalWidth ≤
            TerminalBootstrap.address L.base r ∧
          2*tags.length*(X.positions+1) < 2^w ∧
          TerminalPrefix.arcCount Y ≤ slotCapacity L ∧ TerminalPrefix.arcCount Y ≤ tableWords L ∧
          Y.totalWidth < 2^w ∧ TerminalBootstrap.cost L.shape B.recordLimit+1+30 ≤ cap ∧
          60 ≤ cap ∧ TraversalController.callFuel B.recordLimit+30 ≤ cap := by
  let K := TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit+1+30 + 60 +
    (TraversalController.callFuel B.recordLimit+30)
  filter_upwards [eventually_packedFit B u b hb hstart 0 (fun _ => 0) (PolynomiallyBounded.const 0),
    eventually_pair_clock K] with n hfit hclock
  intro base lanes labels hD hT A _ f hf w r T X E L z G hc Y ls tags cap
  have hp := pairInput_positions S labels hD
  change X.positions = initialPositions b n at hp
  have fit := hfit labels hD hT A f hf z
  rw [← hp] at fit
  have room := fit.2.1
  have low := fit.1
  change L.base+(2^r)^2-32+32 ≤ 2^w at room
  change endAddress L + 2*words B.recordLimit ls + Y.totalWidth < L.base+(2^r)^2-32 at low
  rw [pow_two] at room low
  have caps := hclock G hc
  change K ≤ cap at caps
  have tables := LiveProgram.PairStages.Group.Auxiliary.selected_table_capacity
    B f hf T hT X z (start n)
  have bootCost := packed_bootCost B (start n) X.positions T
  change TerminalBootstrap.cost L.shape B.recordLimit = _ at bootCost
  have rword : r < w := (by omega : r < r+10).trans_le (Nat.le_self_pow (by decide : 4 ≠ 0) _)
  refine ⟨rword,by omega,by omega,low.le,fit.2.2.2.2,tables.1,tables.2,by omega,?_,?_,?_⟩
  all_goals dsimp only [K] at caps; omega

end PairSimulation.TerminalLayout

end VPVNP
end Computability
end OAI
