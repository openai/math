import OAI.Computability.BorderVNP.DiagonalSignedParticipantMerge
import OAI.Computability.BorderVNP.DiagonalSignedRetainedPacket

/-! # Initializing signed parser placements from actual report and sort memories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open DiagonalTallyAllocation RoutingISA CellSparse

/-- Bind the weighted supplemental records to the unique compact row carrying
this global cell number. A cell that the report program did not visit has no
such records. -/
noncomputable def seedExtras {l : ReportLayout} (rows : List (ReportCell l)) (q : ReportCursor) (c : ℕ) : List Record :=
  if h : ∃ i : Fin rows.length, rows[i].number=c then
    let j := Classical.choose h
    bindingRows rows[j].bundles (rows[j].localStart ((rows.take j.val).foldl (fun z row => row.after z) q))
  else []

/-- The same unique row used by the original native report gives its actual
supplemental section after arbitrary signed count and use guesses. -/
theorem ReportAllocation.seedExtras_owned {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {rows : List (ReportCell l)} {q : ReportCursor} (alloc : ReportAllocation pre post banks l rows q)
    (i : Fin rows.length) :
    seedExtras rows q rows[i].number =
      bindingRows rows[i].bundles (rows[i].localStart ((rows.take i.val).foldl (fun z row => row.after z) q)) := by
  classical
  have witness : ∃ j : Fin rows.length, rows[j].number=rows[i].number := ⟨i,rfl⟩
  rw [seedExtras,dite_eq_left witness]
  obtain ⟨embed,num⟩ := alloc.owned
  have pick : Classical.choose witness=i := by
    apply embed.injective
    apply Fin.ext
    rw [←num,←num]
    exact Classical.choose_spec witness
  exact congrArg (fun j : Fin rows.length => bindingRows rows[j].bundles
    (rows[j].localStart ((rows.take j.val).foldl (fun z row => row.after z) q))) pick

end DiagonalTallyCellReports

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM FragmentRows SignedTaskArena CellPacket CellPacket.Supplement
open CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacketGeometry.History.Native
open DiagonalTallyAllocation DiagonalTallyCellReports TypedTaskBuilder

variable {w C desc team frame offsets ctl live ports : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w} {s : Bank w} {mac : TeamOpcode.Macros w 8}

/-- The original seven-word task declared the dense extent before its later
sparse patch. Its witness uses the actual fixed receiving-bank words, including
this execution's particular streamed report suffix. -/
def denseReportBits (l : TypedTaskBuilder.Layout) (src : ℕ → ℕ) (c : ℕ) : List Bool :=
  List.ofFn fun b : Fin (src (l.offsets+2*l.cables+c)+src (l.tails+c)) => src (src (l.banks+2*c+1)+b.val) == 1

@[simp] theorem denseReportBits_length (l : TypedTaskBuilder.Layout) (src : ℕ → ℕ) (c : ℕ) :
    (denseReportBits l src c).length=src (l.offsets+2*l.cables+c)+src (l.tails+c) := by simp [denseReportBits]

/-- Every scalar in the entire emitted public packet region, including both
inverse rank loads, remains at the same address after the report and the
actual two stable fragment passes. -/
theorem signed_geometry_on_fragment (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q desc) (r : Returns prepareCellReports pub mac s m)
    {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f r.val.2.2 fit cells)
    (place : a.SparsePlacement frame ctl) (gp : SparseGeometry a f offsets ctl)
    (pre : ℕ → ℕ) (fromControls : ∀ z, ctl+37≤z → z<a.cube.header.header → readings m z=pre z)
    (physical : banks.bankStart=a.cube.cellBank) (frameEq : rl.frame=frame)
    (z : ℕ) (lo : ctl+37≤z) (hi : z<a.cube.header.header) :
    readings e.output z=pre z := by
  let equiv := reportReturnEquiv seed mac s
  let tape := equiv.symm r
  have returned := (reportReturnEquiv_spec seed mac s tape).2.2
  rw [show reportReturnEquiv seed mac s tape=r from equiv.apply_symm_apply r,prepareWrites_image] at returned
  have bank := a.open_table_order.1
  have top := a.sparse_order place.cells
  have base := place.beforeControl
  have safe := e.original z (by rw [gp.control]; omega) (.inl (by omega))
  rw [safe,returned]
  exact ((alloc.tape _ _).prepare_geometry_word _ _ (by rw [physical]; omega) (by rw [frameEq]; omega)).trans (fromControls z lo hi)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
