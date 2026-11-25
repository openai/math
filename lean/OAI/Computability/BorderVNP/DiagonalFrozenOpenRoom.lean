import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.PackedFrozenPacketDirectories
import OAI.Computability.BorderVNP.PackedTerminalSignedHeaderDepth

/-! # The whole receiving-cell scanner fits the selected signed task -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

/-- Both the end of the public geometry and the quota for the receiving
calls precede the reader's measured end address in this layout. -/
theorem Layout.open_limits {t : Layout} {w u v k : ℕ} (high : t.endAddress w u v k < 2^w) :
    t.cube.header.header < 2^w ∧ t.before.limit < 2^w := by
  have after : t.before.limit ≤ t.after.start := by
    change t.before.limit ≤ t.before.limit+3*t.cube.cells+7*t.cube.cells+
      t.p.scratchStride*t.cube.cells+t.p.burstStride*t.cube.cells
    omega
  have before : t.before.start ≤ t.before.limit := by rw [t.before.footprint]; omega
  have fresh : t.after.start ≤ t.after.fresh := by rw [t.after.footprint]; omega
  have endFit : t.tallyBits < 2^w := by
    unfold Layout.endAddress Layout.entry Layout.valuation DiagonalResidueRAM.gateBase at high
    omega
  have localFit : t.after.fresh ≤ t.tallyBits := by
    unfold Layout.tallyBits DiagonalTallyAllocation.AfterTasks.localBase
    omega
  have bound := (after.trans (fresh.trans localFit)).trans_lt endFit
  exact ⟨(t.open_table_order.1.trans (t.open_table_order.2.2.trans before)).trans_lt bound,bound⟩

end RoutingISA.SignedTaskArena

namespace Diagonal

open Branch Crossing Cover Packing PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena TeamContraction TeamContraction.ProcessorSlots
open GeometryAdvice CellPacketGeometry CellPacketGeometry.LiveWords Packing.RoutingOutputs PackedHistoryCircuit.Retained
open scoped Classical BorderVNP.Epoch.Cube
set_option maxRecDepth 5200
set_option maxHeartbeats 1800000

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)
    {Entry I O : Type} {slots C : ℕ} (tpl : Template Entry I O slots (C+1))

/-- On the same frozen gate ceiling and static spare-inclusive descriptor
template, the scheduled signed task supplies the real receiving program's
frame, cable endpoints, live-pair and control blocks and both complete
marked original-bundle banks. The only numerical premise from the reader
is its already measured final end address. -/
theorem JointSchedule.frozenSignedTask_openRoom (n l size headerFactor profile ceiling field : ℕ)
    (initial : StartupArena) (dir : Directory.Layout) (u v gates : ℕ) :
    let r := stretch b.ρ n
    let R := b.physical.teamsPred n+1
    let W := b.physical.word n
    let start := CoverScale.initialDepth (Epoch.Cube D) r n
    let T := epochs s.τ n
    let V := CoverScale.sites (Epoch.Cube D) start
    let cables := (boundary S start T).edges+4*(R*V)
    let originals := (epochCopies S)^T*V
    let live := R*V
    let depth := BottomReports.BundleSort.markedDepth C originals
    let ordinary := PackedHistoryCircuit.TerminalCells.signedGridOutputCount cables C originals live 37 (Total tpl.publicDepth tpl.chunkDepth)
    let outputs := ordinary+(2^depth+2^depth)
    let fresh := initial.next+7*dir.candidates
    let dest := Allocation.dest fresh profile ceiling outputs field
    let dirs := SeedPlan.frozenPacketDirectories tpl dest cables originals live depth
    let task := b.frozenSignedTask cube n l size headerFactor initial dir profile ceiling outputs field dirs
    let ptr := bases dest cables C originals
    let ctrl := controlsBase dest cables C originals live
    ( (Epoch.Cube D → Deck (EnrichedOuter.depth S start T+1)) ≃ Fin C ) →
    task.endAddress W u v gates < 2^W →
      task.OpenRoom initial.frame ptr.ends ctrl ptr.livePairs live originals (2^depth) W := by
  intro r R W start T V cables originals live depth ordinary outputs fresh dest dirs task ptr ctrl cellNumber high
  have census : CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)=C :=
    (Fintype.card_congr cellNumber).trans (Fintype.card_fin _)
  have cells : task.cube.cells=C := census
  have edges : task.cube.cables=cables := rfl
  have direct := openRoom_of_appended_banks task initial.frame fresh profile ceiling originals live
    tpl.publicDepth tpl.chunkDepth depth field W tpl.chunkLabels.length
  dsimp only at direct
  rw [cells,edges] at direct
  have low : initial.frame+112 ≤ fresh := by
    dsimp only [fresh,StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
    omega
  have room := Layout.open_limits high
  have head : task.cube.header.header=Allocation.stop fresh profile ceiling outputs field W := rfl
  have stop : Allocation.stop fresh profile ceiling outputs field W < 2^W := head ▸ room.1
  refine direct low head stop rfl rfl (Nat.le_pow_clog (by decide : 1<2) _) ?_ le_rfl room.2
  change C ≤ task.cube.cells
  exact cells.ge

end Diagonal

end BorderVNP
end Computability
end OAI
