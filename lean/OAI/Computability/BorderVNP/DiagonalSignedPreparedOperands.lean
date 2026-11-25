import OAI.Computability.BorderVNP.DiagonalSignedArgumentReadback

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Report operands and raw lookup words on one complete signed preparation -/

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM FiniteEvaluator RoutingISA.Evaluator DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyRAM DiagonalTallyMaterialize BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks
open private supplied_unchanged from OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (a : Layout) (team offsets ctl live ports : ℕ)
    (owner : Fin a.cube.header.d → ℕ) (demand : ℕ)
    (A : Data a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s)
set_option quotPrecheck false
local notation "X" => gadgetLookup a pub owner team demand A
local notation "head" => (pub 0).val
local notation "controlRows" => a.controlRows team head offsets ctl live ports

/-- These are exactly the three dynamic inputs of the final operand scan,
on the memory reached by the entire argument writer of the native team. -/
theorem prepared_operands_on_visits {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {description : ℕ} {banks : CellBanks.Layout} (V : SignedPrep.Visits a.id pub mac s m)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after banks l cs q)
    (deck : CubePacket.WordPrepared X a.id pub V.owned.val.2.2)
    (H : OpenSuffix.Inputs) (openPlace : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (openReady : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (packet : A.packetBase=a.cube.header.packetBase)
    (start : banks.bankStart=a.cube.cellBank) (count : banks.cells=a.cube.cells) (stride : banks.stride=a.cube.cellStride)
    (zero : l.zeroAddr=a.cube.stop) (wpos : 0<w) (dim : l.parameters+l.gadgets≤2^w) (width : l.countWidth≤w)
    (source : ∀ c∈cs, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w)
    (sortedLo : head+112≤(controlRows).sorted) (sortedHi : (controlRows).sorted+(controlRows).padded≤a.cube.header.packetBase)
    (ctlLo : head+112≤ctl) (ctlHi : ctl+37≤a.cube.header.packetBase)
    {u v k : ℕ} (place : a.SparsePlacement head ctl)
    (fit : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).Fits w (readings V.reports.val.2.2))
    (pointer : readings V.reports.val.2.2 (head+92)=ctl)
    (controls : ∀ j : Fin 37, readings V.reports.val.2.2 (ctl+j.val)=a.controls j.val)
    (nc : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).host.count=a.cube.cables)
    (nr : readings V.reports.val.2.2 (head+9)≤a.cube.maxRows) (cc : readings V.reports.val.2.2 (head+11)=a.cube.cells)
    (space : a.endAddress w u v k<2^w)
    {Site : Type} (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (production : let parts := (ScheduleClock.argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
      ∃ src : ScheduleClock.SparseCallInput pub parts.2.1.val.2.2,
        ScheduleClock.ProducedRoster a controlRows (readings parts.1.val.2.2) placed geom extra src) :
    let rows := cellsOfTape cs ((reportReturnEquiv seed mac V.controls.val.2.1).symm V.reports)
    CubePacket.WordPrepared X a.id pub V.arguments.val.2.2 ∧
      supplied V.arguments.val.2.2 (cellEnd rows q) q.descriptors (cellOperands rows q) ∧
      (V.arguments.val.2.2 (head+35)).val=(cellOperands rows q).length := by
  intro rows
  obtain ⟨src,produced⟩ := production
  have keep := ScheduleClock.arguments_saved_word a team offsets ctl live ports V.arguments place fit pointer controls
    nc nr cc space placed geom extra src produced
  have readyDeck := wordPrepared_on_reports a owner team demand A V H deck packet (ctlLo.trans (by omega))
    openPlace openReady seed alloc seed.framePointer.symm start count stride
  have actual : ReportAllocation a.before a.after banks l rows q := alloc.tape _ _
  have lo : a.cube.header.packetBase≤a.cube.cellBank := by
    have base := a.cube.group_order.1
    have sp := a.cube.separated
    have b : a.cube.pairBase ≤ a.cube.cellBank := Nat.le_add_right ..
    have p : a.cube.header.packetBase ≤ a.cube.packetEnd := Nat.le_add_right ..
    have q : a.cube.packetEnd ≤ a.cube.singleBank := by unfold CubeArena.Layout.singleBank; omega
    omega
  have past : a.cube.stop<a.fragments.start := by
    change a.cube.stop < CubeConstants.arenaEnd a.cube.stop a.id
    simp only [CubeConstants.arenaEnd,CubeConstants.idBase]
    omega
  have before := a.literal_bounds.2
  have cb := a.literal_bounds.1
  have cd : a.cube.cellBank≤a.cube.stop := cb ▸ Nat.le_add_right ..
  have frame := seed.framePointer
  have hz : a.cube.stop ≠ l.frame+35 := by have h := alloc.frameBefore; omega
  have zd := alloc.read_before_tasks seed mac _ V.reports a.cube.stop hz (.inr (by rw [start,count,stride,cb]; omega))
  have passed : (V.controls.val.2.2 l.zeroAddr).val=0 := by rw [zero,←zd]; exact readyDeck.zero
  obtain ⟨os,num⟩ := receivedOperands alloc seed mac _ V.reports start count stride zero passed wpos dim width source
  constructor
  · apply CubePacket.WordPrepared.transfer X readyDeck
    intro addr read
    rcases gadgetLookup_readAt a pub owner team demand A packet read with ⟨j,hj,rfl⟩ | h | h
    · simp only [CubePacket.frameWords,List.mem_cons,List.not_mem_nil,or_false] at hj
      exact keep _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega))
    · exact keep _ (by omega) (by omega) (.inr (by omega)) (.inl (by omega))
    · change a.cube.stop ≤ addr ∧ addr<a.fragments.start at h
      exact keep _ (by omega) (by omega) (.inr (by omega)) (.inl (by omega))
  constructor
  · apply supplied_unchanged V.reports.val.2.2 _ _ _ (cellOperands rows q) os
    intro addr read
    obtain ⟨lower,region⟩ := actual.signedOperand_region addr read start count stride zero
    exact keep addr (by omega) (by omega) (.inr (by omega)) region
  · exact (congrArg Fin.val (keep _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega)))).trans num

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
