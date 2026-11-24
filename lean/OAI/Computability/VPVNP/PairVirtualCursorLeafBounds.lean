import OAI.Computability.VPVNP.LiveVirtualPairContinuation
import OAI.Computability.VPVNP.PairSimulationLeafBootClock
import OAI.Computability.VPVNP.PairSimulationLeafImageHandler
import OAI.Computability.VPVNP.PairSimulationNominationAssembly

/-! # Resource bounds for the native leaves of a virtual pair -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafVisit

open BurstRAM CursorNetwork CursorRouting LeafStartup LocalHistory

variable {n d e w a H s : ℕ} [NeZero d] {L : PrimedInputRAM.Lengths}
    {Q : PrimedInputRAM.Layout L n a H w}

/-- The native cursor decoder, stack interpreter and initializer use the
same dimensions and private fuel as the selected auxiliary counter. -/
structure CursorLeafBounds (aux : PrimedCounter.Data Q s) (cap : ProcessorBudget n d e w) : Prop where
  clock : NominationClock aux cap.tags cap.capFits (n^39)
  width : d ≤ w
  time : ∀ (v : Position d) (buf : Buffers d (2^e) w),
    steps 52 (auxiliary aux cap.tags cap.capFits v buf) ≤ n^39
  room : ∀ (v : Position d) (buf : Buffers d (2^e) w) j,
    (auxiliaryBank aux cap.tags cap.capFits v buf j).length + n^39 ≤ n^40
  boot : ∀ (v : Site d) (buf : Buffers d (2^e) w),
    LeafBoot.ticks aux cap.tags cap.capFits v buf ≤ n^15

end PairSimulation.LeafVisit

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CursorBounds CursorNetwork CutSchedule ExponentTrace Filter LiveProgram
open PairSimulation

variable {K : Type*} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant)

/-- A single input-length threshold applies to every physical nomination,
pair index, site and independently supplied half-wire buffer. -/
theorem eventually_virtualCursorLeafBounds :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      [NeZero (virtualBits D.addressFactor n)] {ht : 21 ≤ 2^(D.geometry n).w} {clk : 44 ≤ n^10000}
      (adv : Bits (n^D.constants.advicePower)) (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower))
      (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk)),
      LeafVisit.CursorLeafBounds (V.data adv ξ i (physicalNomination rfl μ)) V.cap := by
  filter_upwards [LeafVisit.eventually_resources, LeafBoot.eventually_ticks] with n resources boot
  intro hn V inst ht clk adv ξ i μ
  let nom := physicalNomination rfl μ
  let aux := V.data adv ξ i nom
  have work := (V.counts i (PairedChain.headers adv ξ i) nom).privateWork
  change 6 * aux.fuel ≤ n^10 at work
  have fuel : aux.fuel ≤ n^10 := (Nat.le_mul_of_pos_left _ (by decide : 0 < 6)).trans work
  have h := resources _ _ _ V.cap _ _ _ _ (V.layout i) aux fuel
  have fit := V.cap.capFits
  rw [← pow_add] at fit
  have dim := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp fit
  exact ⟨fun v z => (h v (halfBuffers v z)).1, (Nat.le_add_right ..).trans dim.le,
    fun v buf => (h v buf).1, fun v buf => (h v buf).2,
    fun v buf => boot aux V.cap.tags V.cap.capFits v buf V.cap fuel⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
