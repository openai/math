import OAI.Computability.BorderVNP.DiagonalSignedSparseVisit
import OAI.Computability.BorderVNP.DiagonalSignedReportPacketMemory

/-! # The two real task headers on a returning signed report and fragment scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM FragmentRows SignedTaskArena CellPacket CellPacket.Supplement
open DiagonalTallyAllocation DiagonalTallyCellReports TypedTaskBuilder

variable {w description team frame offsets ctl live ports : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w} {s : Bank w} {mac : TeamOpcode.Macros w 8}
    {source : ℕ → ℕ}
local notation "R" => a.controlRows team frame offsets ctl live ports

/-- Both the four supplemental control words and the seven typed task words
are the physical rows for the same compact owned ordinal after an arbitrary
signed report, real fragment sort, and native task builder. -/
theorem signed_producer_merge_rows {Site : Type} (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description) (r : Returns prepareCellReports pub mac s m)
    {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f r.val.2.2 fit cells)
    (patch : SparsePatch (w:=w) Site (R) (readings e.output))
    (controls : (R).Room w) (image : readings m=(R).published source)
    (physical : banks.bankStart=a.cube.cellBank) (frameEq : rl.frame=frame)
    (place : a.SparsePlacement frame ctl) (geomPhysical : SparseGeometry a f offsets ctl)
    {i : ℕ} (member : i<(R).before (readings e.output) (R).cells) :
    let raw := readings e.output
    let c := globalCell (R).toLayout raw i
    let o := Batch.produced (R) raw patch.placed patch.geometry patch.extra i
    raw ((R).offsets+2*(R).cables+c)+raw ((R).tails+c)=(patch.placed c).external.length →
      o.typed.Stored patch.built (R).tasks i ∧
      WordsAt (readings patch.built) ((R).four+4*i) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords] ∧
      o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length=o.layout.tail := by
  intro src c o wires
  let equiv := reportReturnEquiv seed mac s
  let tape := equiv.symm r
  have returned := (reportReturnEquiv_spec seed mac s tape).2.2
  rw [show reportReturnEquiv seed mac s tape=r from equiv.apply_symm_apply r, prepareWrites_image] at returned
  have lowRead (z : ℕ) (below : z<banks.bankStart) (away : z≠rl.frame+35) : readings r.val.2.2 z=readings m z := by
    rw [returned]
    exact (alloc.tape _ _).prepare_geometry_word _ _ below away
  have midRead (z : ℕ) (lower : a.before.merged≤z) (upper : z<a.before.limit) : readings r.val.2.2 z=readings m z := by
    rw [returned]
    apply writes_outside
    intro x hx
    rw [prepareWrites,List.mem_append] at hx
    rcases hx with yes|yes
    · rcases (alloc.tape _ _).outsideMiddle x yes with lo|hi
      · exact .inr (lo.trans lower)
      · have above : a.after.start≤a.after.packed := by
          simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
        exact .inl (upper.trans_le (alloc.preBefore.trans (above.trans hi)))
    · obtain rfl := List.mem_singleton.mp yes
      have frameLo := alloc.frameBefore
      have bank := alloc.bankBefore
      have middle : a.before.start≤a.before.merged := by
        simp only [BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]; omega
      exact .inr (by change rl.frame+35+1≤z; omega)
  have writer := a.cube.writer_order
  have order := a.sparse_order place.cells
  have base := place.beforeControl
  have below := place.beforeBank
  have above : a.cube.pairBase≤a.cube.cellBank := Nat.le_add_right ..
  have owners (j : ℕ) (hj : j<(R).cells) : (R).owner src j=(R).owner source j := by
    let addr := (R).banks+2*j
    have jlt : j<a.cube.cells := hj
    have start : addr < banks.bankStart := by dsimp only [addr]; change a.cube.hostDirectory+2*j<banks.bankStart; rw [physical]; omega
    have hi : addr < a.fragments.start := (physical ▸ start).trans_le (order.1.trans order.2.1)
    have after : a.cube.header.header ≤ addr := by dsimp only [addr]; change _ ≤ a.cube.hostDirectory+2*j; omega
    have clear : addr ≠ (f).control+29 := by
      have bound := geomPhysical.controller
      rw [geomPhysical.control]
      omega
    have beforeRow : readings m addr=source addr := by
      rw [image,CellControlRows.Layout.published]
      have away := controls.inputApart j hj addr (.inl rfl)
      rw [Function.update_of_ne (fun eq => away (.inr (.inr eq))),CellControlRows.image_outside _ _ le_rfl away]
    have earlier := geomPhysical.controller
    change src addr=source addr
    exact (e.original addr clear (Or.inl hi)).trans ((lowRead addr start (by rw [frameEq]; omega)).trans beforeRow)
  have lower : a.fragments.limit≤a.before.four := by
    have off : a.fragments.limit=a.before.tailWidths := rfl
    have bounds := a.before.ordered
    omega
  have frag : a.fragments.start≤a.fragments.limit := by rw [a.fragments.footprint]; omega
  have held (j : ℕ) (hj : j<(R).before source (R).cells) (k : ℕ) (hk : k<4) :
      src ((R).four+4*j+k)=(R).published source ((R).four+4*j+k) := by
    have jl : j<a.cube.cells := hj.trans_le ((R).before_le source (R).cells)
    have enough : a.cube.cells≤a.before.bound.cells := place.cells
    have bound := a.before.ordered.2.2.2.2.1
    let addr := (R).four+4*j+k
    have lo : a.before.four≤addr := by change _ ≤ a.before.four+4*j+k; omega
    have clear : addr ≠ (f).control+29 := by rw [geomPhysical.control]; omega
    change src addr=(R).published source addr
    rw [←image]
    exact (e.original addr clear (Or.inr (lower.trans lo))).trans (midRead addr (by have := a.before.ordered; omega) (by change a.before.four+4*j+k<a.before.limit; omega))
  have apart (j : ℕ) (hj : j<(R).before src (R).cells) (k : ℕ) (hk : k<4) : ¬(R).outputAt ((R).four+4*j+k) := by
    let addr := (R).four+4*j+k
    have jl : j<a.cube.cells := hj.trans_le ((R).before_le src (R).cells)
    have pay := a.before.ordered.2.2.2.2.1
    have num : a.cube.cells ≤ a.before.bound.cells := place.cells
    have lo : a.before.four≤addr := by change _ ≤ a.before.four+4*j+k; omega
    have high : addr < a.before.limit := by change a.before.four+4*j+k < _; omega
    change ¬(R).outputAt addr
    rintro (⟨x,_⟩|⟨idx,_,eqn⟩|eqn)
    · change a.before.limit+3*a.cube.cells ≤ addr at x
      omega
    · change addr=a.before.limit+3*idx at eqn
      omega
    · change addr=frame+90 at eqn
      omega
  have cellRange := (global_spec (R).toLayout src member).1
  have span : src ((R).sorted+(R).padded+((R).stops+c))-src ((R).sorted+(R).padded+c)-1=
      3*((patch.placed c).parts.length+3) := patch.span c cellRange
  exact Batch.producer_rows (R) source src patch.built patch.placed patch.geometry patch.extra controls patch.room
    patch.image owners held apart member (by change src ((R).sorted+(R).padded+c)<src ((R).sorted+(R).padded+((R).stops+c)); omega) span wires

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
