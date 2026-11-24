import OAI.Computability.VPVNP.LiveVirtualPairPaperDescriptor
import OAI.Computability.VPVNP.LiveVirtualPairNativeAssembly
import OAI.Computability.VPVNP.LiveTerminalProtectedAddresses
import OAI.Computability.VPVNP.LiveCompressedPairOnlineWord
import OAI.Computability.VPVNP.PairTerminalLowCells
import OAI.Computability.VPVNP.PairTerminalPackedPrefix

/-! # The counter words presented to the selected terminal vertices -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM LiveProgram LocalCount
open PairStages PairStages.Group PairStages.Group.CompressedPaths CompressedPair
open PairSimulation PairSimulation.LocalHistory NetworkKernel CompressorRecords CompressorRecords.Schedule

set_option quotPrecheck false
open scoped Fin.CommRing

attribute [local irreducible] CompressedPair.regs CompressedPair.components TerminalProgram.workers
set_option maxHeartbeats 1200000

variable {D : FixedProgramDiagonal.Program} {n C : ℕ} {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
    {K : Type} [Field K] {S : BlockSchedule K} {B : S.Templates} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)

local notation "grp" => D.executionGroup n ht hf
variable (W : Conditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (P : PairStageConditions (D.executionGroup n ht hf) (2^(D.geometry n).d) (D.geometry n).H)
    (hC : D.constants.circuitExponent = C) (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (cut : 1+B.denseCount n C*D.counterWidth n ≤ n^D.constants.deltaPower)
    (I : VirtualPairs.PhysicalInput data W P hC hg cut)
local notation "mem" => I.branch.copy.memory ()
local notation "sel" => V.selection (M := M)
local notation "ws" => PublicExpr.eval (D.geometry n) (Layout.pairWorkspace D.constants)
local notation "ports" => publicWords grp

local notation "f" => B.compressorValues hn M
local notation "hf₀" => B.compressorValues_solution hn M
local notation "T" => blockCount (u.θ : ℝ) n
local notation "positions" => initialPositions D.addressFactor n
local notation "L" => BlockProgram.layout B ws positions T
local notation "boot" => paperBootstrap B u
local notation "script" => BlockProgram.script B

variable (rate : ℕ)
variable (Y : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M) D.constants hg
  ((Layout.pairWorkspace D.constants).eval (D.geometry n)) (fuel (D.executionGroup n ht hf)) rate
  (publicWords (D.executionGroup n ht hf)) (I.branch.copy.memory ()))

open TerminalLink SourceTransport
open CompressorRecords.DescriptorSpace (endAddress levelStart levelsBase directoryBase plannerTag frameBase tableBase arrayBase incidenceStart)

/-- Each selected shared-bit assignment reaches the vertex phase with the
same grammar and motif counter words that the pair received on entry. -/
theorem VirtualPairs.PaperDescriptor.vertex_counter_initial (z : (sel).Choices)
    (setup : TransferredStartup.Runs (bootstrapRows boot (script).initial.length (script).block.length) (script).size
      (startupLayout boot (script).initial.length (script).block.length D.addressFactor n ws)
      D.addressFactor n (S.degreeExponent 0) S.laneBits S.steps ports (PairTag.address ports) mem)
    (workspace : ws < 2^(D.geometry n).w)
    {tab : Fin (L).shape.tables} {baseBits laneBits : ℕ} {bits : Fin ((sel).finalState z).totalWidth → Bool}
    {vertex : Memory (grp).w}
    (entry : TerminalProgram.VertexEntry B f hf₀ T le_rfl V.scanState z L tab baseBits laneBits
      ports (onlinePost (Y.paths z)) vertex bits) (j : Fin (labelCount grp)) :
    vertex (Auxiliary.counterBase grp+j.val) = mem (Auxiliary.counterBase grp+j.val) := by
  let a := Auxiliary.counterBase grp+j.val
  have tag := (terminal_protected_addresses grp (ports 2).val workspace le_rfl).1.1
  have wsVal : (ports 2).val = ws := Nat.mod_eq_of_lt workspace
  have sh : Auxiliary.shadowBase grp < ws := Nat.lt_add_of_pos_right (Nat.two_pow_pos _)
  have apart : a < (PairTag.address ports).val := counter_before_pairTag grp (sh.trans workspace) j
  have low : a < ws := (apart.trans tag).trans_eq wsVal
  have base : (L).base = ws := rfl
  have raw := entry.raw a (by
    unfold endAddress levelStart levelsBase directoryBase plannerTag frameBase
    omega) (.inl (by
    unfold tableBase arrayBase incidenceStart levelStart levelsBase directoryBase plannerTag frameBase
    omega))
  have below : (PairTag.address ports).val < (ports 2).val+6 := by omega
  exact raw.trans ((Y.protectedOnline below).after_startup_word D.addressFactor n ws mem setup Y.init
    (Y.paths z) a low apart.ne (Y.online_word below a (by omega)))

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
