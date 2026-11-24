import OAI.Computability.VPVNP.PairVirtualDescriptorHistory
import OAI.Computability.VPVNP.PairVirtualPaperPreparedInput
import OAI.Computability.VPVNP.PairVirtualEventualChecks
import OAI.Computability.VPVNP.PairVertexRatedBoundarySelection
import OAI.Computability.VPVNP.LiveCompressedPairOnlineWord

/-! # Role checks at the terminal boundary of a physical pair -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM CursorBounds CursorNetwork Compression LabelEvaluator LiveProgram LocalCount
open PairStages PairStages.Group PairStages.Group.Auxiliary PairStages.Group.CompressedPaths
open CompressedPair PairSimulation LocalHistory CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles CutSchedule ExponentTrace NetworkKernel
open scoped Fin.CommRing
set_option quotPrecheck false

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
  {B : S.Templates} {u : PairExponents B.growthConstant} {n : ℕ} {hn : 2 ≤ n}
  {ht : 21 ≤ 2 ^ (D.geometry n).w} {clk : 44 ≤ n ^ 10000} {p : Nat.Primes}
  {model : Model p (B.compressorDegree n) (B.compressorEquations hn D.constants.circuitExponent)}
  {data : D.ScalarData B hn model} {V : D.VirtualPairs B u hn D.constants.circuitExponent}
  [NeZero (virtualBits D.addressFactor n)]
  {ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower)} {i : D.groupIndices n}
  {μ : Nominations.Nom (D.executionGroup n ht clk)}
  (scan : CanonicalScan data V ξ i (physicalNomination rfl μ))
  {hg : D.constants.motifLabels = Fintype.card B.Entry} {rate : ℕ}
  {input : Memory (wordBits D.addressFactor n)}

local notation "G₀" => D.executionGroup n ht clk
local notation "start₀" => (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
local notation "pub₀" => publicWords (G₀)
local notation "κ₀" => B.compressorValues hn model
local notation "ok₀" => B.compressorValues_solution hn model
local notation "T₀" => blockCount (u.θ : ℝ) n
local notation "X₀" => V.scanState
local notation "pos₀" => initialPositions D.addressFactor n
local notation "L₀" => BlockProgram.layout B (start₀) (pos₀) (T₀)
local notation "base₀" => virtualBits D.addressFactor n - reservedLanes B u n
local notation "lanes₀" => reservedLanes B u n
local notation "order₀" => entryOrdinal B D.constants hg
local notation "boot₀" => paperBootstrap B u
local notation "script₀" => BlockProgram.script B

variable (receipt : V.PaperDescriptor (B.compressorValues hn model)
    (B.compressorValues_solution hn model) D.constants hg
    ((LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n))
    (fuel (D.executionGroup n ht clk)) rate (publicWords (D.executionGroup n ht clk)) input)
  (z : (V.selection (M := model)).Choices)

attribute [local irreducible] TerminalProgram.workers CompressedPair.regs BlockProgram.script
  BlockProgram.layout VertexImage.template VertexImage.placement BlockSchedule.Templates.execute
  CursorNetwork.cursorState CursorBounds.wordBits

/-- All three roles at every site of the selected branch, in the order used
by the fixed terminal instruction table. -/
abbrev CanonicalScan.PaperRoleBoundary : Prop :=
  let tab : Fin (L₀).shape.tables := ⟨0, by unfold BlockProgram.layout; change 0 < 6; decide⟩
  let Y := (V.selection (M := model)).finalState z
  let payload := CompiledResident.payload (w := (D.geometry n).w) B κ₀ ok₀
    ((start₀ : ℕ) : BurstRAM.Word (D.geometry n).w) pos₀ T₀ n
  ∀ bits reference, TerminalProgram.VertexEntry B κ₀ ok₀ T₀ le_rfl X₀ z L₀ tab
    base₀ lanes₀ pub₀ (onlinePost (receipt.paths z)) reference bits →
    SelectedPayloadHistory.Past B κ₀ ok₀ L₀ payload
      (executeLevels B κ₀ ok₀ T₀ le_rfl X₀ z) reference →
    ∀ (j : Fin (siteOrder Y).length) m, LinkedVertexMemory G₀ reference j.val m →
      V.SelectedRowsAt data.advice ξ i μ order₀ κ₀ ok₀ scan.leafSites z m 1
        (VertexImage.RatedRoles.scan B order₀)

omit [NeZero (virtualBits D.addressFactor n)] in
/-- The real startup and calendar preserve the prepared input words read by the leaf reader. -/
theorem VirtualPairs.PaperDescriptor.calendar_input_below
    (setup : TransferredStartup.Runs
      (bootstrapRows boot₀ (script₀).initial.length (script₀).block.length) (script₀).size
      (startupLayout boot₀ (script₀).initial.length (script₀).block.length D.addressFactor n start₀)
      D.addressFactor n (S.degreeExponent 0) S.laneBits S.steps pub₀ (PairTag.address pub₀) input)
    (workspace : (pub₀ 2).val = start₀) (tag : (PairTag.address pub₀).val < (pub₀ 2).val)
    (x : ℕ) (low : x < (pub₀ 2).val) (apart : x ≠ (PairTag.address pub₀).val) :
    onlinePost (receipt.paths z) x = input x := by
  have below : (PairTag.address pub₀).val < (pub₀ 2).val + 6 := by omega
  exact (receipt.protectedOnline below).after_startup_word D.addressFactor n start₀ input setup
    receipt.init (receipt.paths z) x (low.trans_eq workspace) apart
    (receipt.online_word below x (by omega))

open Filter

private theorem eventually_role_startup (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant)
    (lanes : S.laneBits ≤ D.addressFactor)
    (num : D.numerator = (liveRatio u).num) (den : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (ht : 21 ≤ 2 ^ (D.geometry n).w) (clk : 44 ≤ n ^ 10000),
      let G := D.executionGroup n ht clk
      let pub := publicWords G
      let ws := (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
      let boot := paperBootstrap B u
      let script := BlockProgram.script B
      (pub 2).val = ws ∧ (PairTag.address pub).val < (pub 2).val ∧ ∀ m,
        TransferredStartup.Runs (bootstrapRows boot script.initial.length script.block.length)
          script.size (startupLayout boot script.initial.length script.block.length
            D.addressFactor n ws) D.addressFactor n (S.degreeExponent 0) S.laneBits S.steps
          pub (PairTag.address pub) m := by
  let base := fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
  have bounds : PolynomiallyBounded base := by
    have eqn : base = fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval
        (paperGeometry D.addressFactor (liveCapacity u) n) := by
      funext n
      change (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n) = _
      rw [paperGeometry_eq D B u num den n]
    rw [eqn]
    exact startup_workspace_polynomial _ D.address_pos (liveCapacity_polynomial u)
  have frac : ((blockRatio u).num : ℝ) / (blockRatio u).den ≤ 1 := by
    rw [(blockRatio u).value]
    exact_mod_cast (le_trans u.theta_lt.le (by norm_num))
  let boot := paperBootstrap B u
  let script := BlockProgram.script B
  have arity : 7 ≤ boot.shape.arity := (by decide : 7 ≤ 11).trans (InitialTransferred.arity B)
  have scalars : 30 ≤ boot.shape.scalarFields := by change 30 ≤ 54; decide
  have phases : 0 < (bootstrapRows boot script.initial.length script.block.length).phaseRows := by
    unfold script BlockProgram.script
    exact InitialTransferred.phases_pos B
  have runs := TransferredStartup.eventually_run
    (bootstrapRows boot script.initial.length script.block.length) script.size boot.shape
    D.addressFactor (S.degreeExponent 0) S.laneBits S.steps D.address_pos (blockRatio u).den_pos
    phases frac lanes arity scalars bounds
  filter_upwards [runs, eventually_startup_inputs D.constants D.address_pos
    (liveCapacity_polynomial u)] with n started ready
  intro ht clk G pub ws boot' script'
  have actual := ready G.lit
  rw [← paperGeometry_eq D B u num den n] at actual
  obtain ⟨workspace, length, width, tag⟩ := actual
  change (pub 2).val = ws at workspace
  change (PairTag.address pub).val < (pub 2).val at tag
  exact ⟨workspace, tag, started pub (PairTag.address pub) workspace length width
    (tag.trans_eq workspace)⟩

set_option maxHeartbeats 900000 in
-- The branch, the prepared header and the dependent directory must agree simultaneously.
/-- One threshold supplies the terminal role readers for every physical nomination,
selected compressor path and reached site in every realization at that length. -/
theorem eventually_paperRoleBoundary (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant)
    (labels : D.constants.motifLabels = Fintype.card B.Entry)
    (addr : max S.laneBits 5 ≤ D.addressFactor)
    (num : D.numerator = (liveRatio u).num) (den : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      [NeZero (virtualBits D.addressFactor n)]
      (ht : 21 ≤ 2 ^ (D.geometry n).w) (clk : 44 ≤ n ^ 10000)
      {p : Nat.Primes} {model : Model p (B.compressorDegree n)
        (B.compressorEquations hn D.constants.circuitExponent)}
      (data : D.ScalarData B hn model),
      let G := D.executionGroup n ht clk
      let sites := 2 ^ (D.geometry n).d
      let cap := (D.geometry n).H
      ∀ (W : Conditions G sites cap) (P : PairStageConditions G sites cap)
        (cut : 1 + B.denseCount n D.constants.circuitExponent * D.counterWidth n ≤
          n ^ D.constants.deltaPower)
        (I : VirtualPairs.PhysicalInput data W P rfl labels cut),
        let ext := VirtualPairs.exterior data W P rfl labels cut I
        let idx := VirtualPairs.modelIndex data W P rfl labels cut I
        let start := (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
        let f := B.compressorValues hn model
        let ok := B.compressorValues_solution hn model
        ∀ (A : CanonicalScan data V ext idx (physicalNomination rfl I.μ)) (rate : ℕ)
          (receipt : V.PaperDescriptor f ok D.constants labels start (fuel G) rate
            (publicWords G) (I.branch.copy.memory ())) (z : (V.selection (M := model)).Choices),
          A.PaperRoleBoundary receipt z := by
  let order := entryOrdinal B D.constants labels
  filter_upwards [eventually_activeChecks D B u order labels addr num den,
    eventually_role_startup D B u ((Nat.le_max_left _ _).trans addr) num den]
    with n checks startup
  intro hn V inst ht clk p model data G sites cap W P cut I ext idx start f ok A rate receipt z
    bits reference entry _ j m later
  obtain ⟨workspace, tag, setup⟩ := startup ht clk
  obtain ⟨prepared, copy⟩ := VirtualPairs.paperPreparedInput data W P labels cut I
  have positions : V.scanState.positions = initialPositions D.addressFactor n := by
    rw [V.scanState_pairInput]
    exact pairInput_positions S _ _
  have history := receipt.past_calendar z workspace (tag.trans_le (Nat.le_add_right _ _))
  have ws : (terminalOperands G 2).val = start := workspace
  apply checks hn V ht clk data ext idx I.μ A z prepared
    (tab := ⟨0, by unfold BlockProgram.layout; change 0 < 6; decide⟩)
    (bits := bits) (reference := reference) (ord := j.val)
    (calendar := onlinePost (receipt.paths z))
  · let blocks := blockCount (u.θ : ℝ) n
    have same : BlockProgram.layout B start (initialPositions D.addressFactor n) blocks =
        BlockProgram.layout B (terminalOperands G 2).val V.scanState.positions blocks := by
      rw [ws, positions]
    exact entry.changeLayout same
      (tab' := ⟨0, by unfold BlockProgram.layout; change 0 < 6; decide⟩) rfl
  · exact history
  · exact later
  · intro x low apart
    exact (receipt.calendar_input_below z (setup _) workspace tag x low apart).trans
      (congrFun copy.symm x)

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
