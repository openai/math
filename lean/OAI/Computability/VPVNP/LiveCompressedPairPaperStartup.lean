import OAI.Computability.VPVNP.LiveCompressedPairPaperTable
import OAI.Computability.VPVNP.CompressorInitialLiveBoundary
import OAI.Computability.VPVNP.FixedProgramParameters
import OAI.Computability.VPVNP.LiveVirtualPairOccurrence

/-! # Starting the chosen fixed pair on the live group's memory

A single threshold applies to every header, nomination, coefficient ring
and solution at every larger length. The first eight calls supply the
transferred startup needed by the frame proofs and the initial resident
boundary needed by the descriptor scheduler.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

universe v
open Compression CursorBounds CursorNetwork BurstRAM LiveProgram LiveProgram.CompressedPair
open CompressorRecords PairStages.Group.CompressedPaths

variable {K : Type} [Field K] {S : BlockSchedule K} (B : S.Templates)
  (u : PairExponents B.growthConstant) (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry)
  (E : UniversalMachine.Program) (addr : ℕ) (positive : 1 ≤ addr)

/-- The fixed live table, using the concrete pair body and the chosen address multiplier. -/
def paperProgram :=
  ofPaperConstants c E (paperTable B u c labels) addr positive (liveRatio u)

local notation "D" => paperProgram B u c labels E addr positive
local notation "boot" => paperBootstrap B u
local notation "A" => BlockProgram.script B

/-- The startup certificate before inspecting any descriptor branch. -/
def PaperStartup (n : ℕ) (ht : 21 ≤ 2^((D).geometry n).w) (hf : 44 ≤ n^10000)
    (m : Memory (wordBits addr n)) (hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0)) : Prop :=
  let G := (D).executionGroup n ht hf
  let pub := publicWords G
  let base := (LiveProgram.Layout.pairWorkspace c).eval ((D).geometry n)
  base < 2^(wordBits addr n) ∧
    TransferredStartup.Runs (bootstrapRows boot (A).initial.length (A).block.length) (A).size
      (startupLayout boot (A).initial.length (A).block.length addr n base) addr n (S.degreeExponent 0)
      S.laneBits S.steps pub (PairTag.address pub) m ∧
    ∀ {R : Type v} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      ScheduledTrace.InitialLive B f hf (blockRatio u).num (blockRatio u).den addr n base (fuel G)
        (paperTerminal B u c labels) pub m hd

/-- The paper's eleven public words and all eight native startup rows at one
common threshold before the length-dependent scalar ring or solution. -/
theorem eventually_paperStartup (lanes : S.laneBits ≤ addr) :
    ∃ hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0),
      ∀ᶠ n : ℕ in Filter.atTop, ∀ (ht : 21 ≤ 2^((D).geometry n).w) (hf : 44 ≤ n^10000)
        (m : Memory (wordBits addr n)),
        m (PairTag.address (publicWords ((D).executionGroup n ht hf))).val = 0 →
        PaperStartup.{v} B u c labels E addr positive n ht hf m hd := by
  let H := liveCapacity u
  let base n := (LiveProgram.Layout.pairWorkspace c).eval (paperGeometry addr H n)
  have hH := liveCapacity_polynomial u
  have hb : PolynomiallyBounded base := startup_workspace_polynomial c positive hH
  have hθ : ((blockRatio u).num : ℝ)/(blockRatio u).den ≤ 1 := by
    rw [(blockRatio u).value]
    exact_mod_cast (le_trans u.theta_lt.le (by norm_num))
  obtain ⟨hd,initial⟩ := ScheduledTrace.eventually_initial_live_uniform B c (paperTerminal B u c labels)
    (blockRatio u).num (blockRatio u).den addr (blockRatio u).den_pos positive hθ lanes hH
  have ha : 7 ≤ (boot).shape.arity := (by decide : 7 ≤ 11).trans (InitialTransferred.arity B)
  have fields : 30 ≤ (boot).shape.scalarFields := by change 30 ≤ 54; decide
  have runs := TransferredStartup.eventually_run (bootstrapRows boot (A).initial.length (A).block.length)
    (A).size (boot).shape addr (S.degreeExponent 0) S.laneBits S.steps positive (blockRatio u).den_pos
    (InitialTransferred.phases_pos B) hθ lanes ha fields hb
  refine ⟨hd,?_⟩
  filter_upwards [initial,runs,eventually_startup_inputs c positive hH] with n ready transferred inputs
  intro ht hf m tag
  let G := (D).executionGroup n ht hf
  obtain ⟨workspace,length,width,below⟩ := inputs G.lit
  change (publicWords G 2).val = base n at workspace
  refine ⟨workspace.symm.trans_lt (publicWords G 2).isLt,
    transferred (publicWords G) (PairTag.address (publicWords G)) workspace length width (below.trans_le workspace.le) m,?_⟩
  intro R _ f hf
  exact ready f hf G.lit m G rfl tag

end FixedProgramDiagonal.Program

namespace LiveProgram.LocalCount
open BurstRAM CutSchedule PairStages PairStages.Group PairStages.Group.CompressedPaths

/-- The actual auxiliary copy supplies the zero linker tag required by the
fixed pair startup, for every valid nominated first-half group. -/
theorem CompressedInput.pairStartTag {G : Group} {S H : ℕ} {W : Conditions G S H} {P : PairStageConditions G S H}
    {adv : Bits (profile G).advice} {fit : 1+labelCount G*expWidth G ≤ (profile G).delta}
    (I : CompressedInput W P adv fit) :
    I.branch.copy.memory () (PairTag.address (publicWords G)).val = 0 :=
  I.branch.startup_tag I.out I.nominationFits I.trace.tag I.μ I.shadowFit

end LiveProgram.LocalCount

end

end VPVNP
end Computability
end OAI
