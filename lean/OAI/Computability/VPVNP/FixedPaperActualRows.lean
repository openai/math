import OAI.Computability.VPVNP.FixedPaperTerminalBounds
import OAI.Computability.VPVNP.LiveVirtualPairQuietFrame
import OAI.Computability.VPVNP.PairVertexPaperRatedSelection
import OAI.Computability.VPVNP.PairVirtualPaperRoleBoundary

/-! # The chosen physical terminal rows of each nominated pair

The three deterministic stages retain the low RAM words on each successful
prefix. The shared-bit stage selects the actual arc payload. The roles of the
visited terminal vertices are verified on that same memory, including its
retained shrinking and refresh records and the virtual coefficient header.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds BurstRAM LiveProgram LiveProgram.CompressedPair Filter
open LabelEvaluator CompressorRecords ScheduledTrace PairStages PairStages.Group PairStages.Group.CompressedPaths
open PairSimulation LocalCount
open scoped Fin.CommRing
set_option quotPrecheck false
attribute [local irreducible] BlockProgram.script BlockProgram.layout CursorNetwork.cursorState
  CompressedPair.stages CompressedPair.regs CompressedPair.components TerminalProgram.workers
  CursorBounds.wordBits BurstRAM.addressWidth Nat.clog CursorBounds.virtualBits
  VertexImage.segments VertexImage.template VertexGeometry.segment ShrinkVertexImage.shrinkSegment
  RefreshVertex.refreshSegment PrimedCounter.renameFlow PrimedInputRAM.Flow.length

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (u : PairExponents B.growthConstant)
  (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry) (E : UniversalMachine.Program)
  (addr : ℕ) (positive : 1 ≤ addr)
local notation "D" => paperProgram B u c labels E addr positive
local notation "names" => entryOrdinal B c labels
local notation "scanRate" => VertexImage.RatedRoles.scan B names

set_option maxHeartbeats 1200000 in
/-- At all sufficiently large lengths the installed terminal table realizes every
selected compressor vertex within its per-site cost, for every model and nomination. -/
theorem eventually_paperRatedRows (raw : ℕ) (enough : max S.laneBits 5 ≤ addr) :
    ∀ᶠ n : ℕ in atTop, PaperRatedRows B u c labels E addr positive raw scanRate n := by
  have preludeBounds := eventually_paperDescriptorQuiet (D) B u c.circuitExponent enough rfl rfl c labels
  have replay := eventually_paperDescriptorQuietFrame (D) B u c.circuitExponent enough rfl rfl c labels
  have site := eventually_rated_at_boundary (D) B u enough rfl rfl labels names
  have role := eventually_paperRoleBoundary (D) B u labels enough rfl rfl
  filter_upwards [preludeBounds,replay,site,role,eventually_startup_inputs c positive (liveCapacity_polynomial u),
    eventually_ge_atTop 128] with n choose frames rated hooks inputs large
  intro hn p M data V inst G W P cut I A base rate Y z
  let ht := (D).tagsFit n
  let hc := dispatchClock hn
  let m := I.branch.copy.memory ()
  let ξ := VirtualPairs.exterior data W P rfl labels cut I
  let i := VirtualPairs.modelIndex data W P rfl labels cut I
  obtain ⟨q,ready⟩ := choose hn V ht hc M rate m Y z
  obtain ⟨ws,_,_,before⟩ := inputs G.lit
  have low : (PairTag.address (publicWords G)).val < (publicWords G 2).val+6 :=
    before.trans_le (Nat.le_add_right _ _)
  refine ⟨q,ready,?_,(frames hn V ht hc M rate m Y z).2 q⟩
  have roleAt := hooks hn V ht hc data W P cut I A rate Y z
  let oracle (online calendar reference memory : Memory ((D).geometry n).w) :=
    rated hn V ht hc data.advice ξ i I.μ M.algebra (B.compressorValues hn M)
      (B.compressorValues_solution hn M) A.leafSites z
      (virtualBits addr n-reservedLanes B u n) (reservedLanes B u n) (initialWidth addr n) n
      1 scanRate online calendar reference memory
  have good := Y.ratedSelection A z rfl rfl q ready large ws low oracle roleAt
  unfold VirtualPairs.PaperDescriptor.RatedTerminalRows at good
  have space : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w := ws.symm.trans_lt (publicWords G 2).isLt
  have old := (tag_before_workspace G.constants G.g).trans space
  change Auxiliary.counterBase G + (Auxiliary.histLength G + G.constants.motifLabels) < 2^G.w at old
  have counterWord : (Auxiliary.terminalOperands G 4).val = Auxiliary.counterBase G :=
    Nat.mod_eq_of_lt (show Auxiliary.counterBase G < 2^G.w by omega)
  have grammarWord : (Auxiliary.terminalOperands G 5).val = Auxiliary.histLength G :=
    Nat.mod_eq_of_lt (show Auxiliary.histLength G < 2^G.w by omega)
  rw [counterWord,grammarWord] at good
  unfold RatedAt
  simp only [TerminalLink.QuietPrefix.reindexWorkers,
    paperSegments,shrinkRole,refreshRole,TerminalProgram.nativeSegments,TerminalProgram.installedSegments,
    G,paperProgram,ofPaperConstants,Auxiliary.terminalOperands,publicWords] at good ⊢
  exact good

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI
