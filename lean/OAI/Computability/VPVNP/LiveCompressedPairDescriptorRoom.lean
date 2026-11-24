import OAI.Computability.VPVNP.LiveCompressedPairPaperStartup
import OAI.Computability.VPVNP.CompressorBlockCapacity
import OAI.Computability.VPVNP.CompressorBlockClock

/-! # Uniform workspace and clock bounds of the concrete pair table

The workspace operand is the evaluated live layout address, uniformly over
the execution group's prefix. The complete block directory and data arenas
fit there at all sufficiently large lengths. The same length bound supplies
the calendar's tag width and fixed overhead on both clocks.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program
open Compression CursorBounds CursorNetwork BurstRAM LiveProgram LiveProgram.CompressedPair Filter
open CompressorRecords DescriptorSpace PairStages.Group.CompressedPaths

variable {K : Type} [Field K] {S : BlockSchedule K} (B : S.Templates) (u : PairExponents B.growthConstant)
variable (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry)
variable (E : UniversalMachine.Program) (addr : ℕ) (positive : 1 ≤ addr)
local notation "D" => paperProgram B u c labels E addr positive

theorem eventually_descriptor_room :
    ∀ᶠ n : ℕ in atTop, ∀ (ht : 21 ≤ 2^((D).geometry n).w) (hf : 44 ≤ n^10000),
      let G := (D).executionGroup n ht hf
      let pub := publicWords G
      let base := (LiveProgram.Layout.pairWorkspace c).eval ((D).geometry n)
      let L := BlockProgram.layout B (pub 2).val (initialPositions addr n) (blockCount (u.θ : ℝ) n)
      (pub 2).val = base ∧ endAddress L < 2^wordBits addr n ∧
        ∀ cap ≥ BlockClock.small B addr n,
          Schedule.Online.Run.ControlBounds (BlockProgram.script B).plan cap (w := wordBits addr n) := by
  let H := liveCapacity u
  let base n := (LiveProgram.Layout.pairWorkspace c).eval (paperGeometry addr H n)
  have hH := liveCapacity_polynomial u
  have bounded : PolynomiallyBounded base := startup_workspace_polynomial c positive hH
  have theta : (u.θ : ℝ) ≤ 1 := by exact_mod_cast (le_trans u.theta_lt.le (by norm_num : (1/100 : ℚ) ≤ 1))
  have room := BlockProgram.eventually_end B addr positive theta bounded (PolynomiallyBounded.const 0)
  filter_upwards [room,BlockClock.eventually_room B addr positive 3,eventually_startup_inputs c positive hH]
    with n fits bounds start ht hf
  let G := (D).executionGroup n ht hf
  obtain ⟨workspace,_,_,_⟩ := start G.lit
  change (publicWords G 2).val = base n at workspace
  refine ⟨workspace,?_,bounds.2⟩
  change endAddress (BlockProgram.layout B (publicWords G 2).val _ _) < _
  rw [workspace]
  simpa only [Nat.add_zero] using fits

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
