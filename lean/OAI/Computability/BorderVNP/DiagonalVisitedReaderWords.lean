import OAI.Computability.BorderVNP.DiagonalNativeOwnerBank
import OAI.Computability.BorderVNP.DiagonalNativeArgumentRoster
import OAI.Computability.BorderVNP.DiagonalProducedRoster
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderReplay

/-! # Protected words through all signed controls, reports, and private task writers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch FiniteEvaluator BorderVNP.Cube DiagonalTallyAllocation
open DiagonalTallyCellReports TeamContraction.ProcessorSlots CellPacket CellPacket.Supplement.Batch
open SignedTaskArena
set_option maxHeartbeats 1600000

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    {a : SignedTaskArena.Layout} {u v k ctl team offsets live ports bundles b description : ℕ}
    {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
local notation "head" => readings pub 0
local notation "H" => a.openInputs team head offsets ctl live ports bundles b owner header
local notation "rows" => a.controlRows team head offsets ctl live ports

/-- A returning public suffix through its actual published compact task list
preserves all low startup banks. Only the report and owned-task counts are
published below the public control directory. -/
def KeptToCalls {w : ℕ} (A : StartupArena) (frame : ℕ) (owned calls : Memory w) : Prop :=
  ∀ x < A.next, x≠frame+35 → x≠frame+90 → calls x=owned x

/-- Inspect the actual emitted reports and all six returning argument stages.
The physical task source bounds the writes of the sparse compressor and typed
serializer at their true destination row, even for a zero-length task list. -/
theorem keptToCalls_on_visits {Site : Type} (A : StartupArena)
    (V : SignedPrep.Visits id pub mac s m) (axis : Fin (a.cube.n+1))
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q)
    (place : a.SparsePlacement head ctl)
    (fit : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).Fits w (readings V.reports.val.2.2))
    (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (words : ∀ i : Fin 37,readings V.reports.val.2.2 (ctl+i.val)=a.controls i.val)
    (cables : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).host.count=a.cube.cables)
    (rawCount : readings V.reports.val.2.2 (head+9)≤a.cube.maxRows)
    (cells : readings V.reports.val.2.2 (head+11)=a.cube.cells) (high : a.endAddress w u v k < 2^w)
    (belowCube : A.next ≤ a.cube.header.header) (belowControl : A.next ≤ ctl)
    (belowGeometry : A.next ≤ a.p.sorted)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) :
    let parts := (argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
    let old := readings parts.1.val.2.2
    ∀ src : SparseCallInput pub parts.2.1.val.2.2, ProducedRoster a rows old p geom extra src →
      KeptToCalls A head V.owned.val.2.2 (SignedPrep.visitsEquiv id pub mac s m V).val.2.2 := by
  intro parts old src roster x hx ne35 ne90
  obtain ⟨bank,_,_,_,_,_,external,counts,_,merged,calls,tasks,_⟩ :=
    a.reader_bounds A team head offsets ctl belowCube
  have cellLow : x < a.cube.cellBank := hx.trans_le bank
  have controls := ((OpenSuffix.run H ready).sound V.controls.property).2
  have ctlWord : V.controls.val.2.2 x = V.owned.val.2.2 x :=
    Fin.ext ((congrFun controls x).trans (a.open_image_low owner header position x cellLow ne90))
  have repWord := report_return_before_cells seed alloc V.reports (x:=x) cellLow
    (by rw [←seed.framePointer]; exact ne35)
  have frWord := fragment_return_before_cells fit ptr words place cables rawCount cells high parts.1 cellLow (by omega)
  obtain ⟨_,_,_,taskRun,_,taskImage⟩ := TypedTaskBuilder.program_run pub mac parts.1.val.2.1 parts.1.val.2.2
    (rows).toLayout rfl roster.fields roster.room
  have im : readings parts.2.1.val.2.2=(rows).toLayout.published old := by
    rw [(parts.2.1.property.unique_of_deterministic (by decide) taskRun).2.2]
    exact taskImage
  let patched := written parts.2.1.val.2.2 src.merge src.count
  have patch : patched x=parts.1.val.2.2 x := by
    dsimp only [patched]
    rw [roster.merge,roster.count]
    exact ReaderKept.afterSupplement_word (rows) parts.1.val.2.2 parts.2.1.val.2.2 p geom extra
      roster.room im roster.span A.next x hx ne90 ⟨calls,tasks,belowGeometry,merged⟩
  have sparse := ReaderKept.afterSparse_word src.layout src.owned src.image A.next x hx (by
    rw [roster.layout]; exact ⟨external,tasks,counts⟩)
  have tab : TypedBatch.written src.compressed src.tasks src.count x=src.compressed x := by
    apply TypedBatch.preserve src.compressed src.tasks (i:=0) (Nat.zero_le _) x
    intro i _ hi
    rw [roster.count] at hi
    exact TypedTaskBuilder.below (rows).toLayout old roster.taskArena hi
      (hx.trans_le (calls.trans ((Nat.le_add_right ..).trans roster.taskArena.calls))) (.inl (hx.trans_le calls))
  have endState := congrArg (fun r : Returns SignedPrep.arguments pub mac V.reports.val.2.1 V.reports.val.2.2 => r.val.2.2)
    ((argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).apply_symm_apply V.arguments)
  change parts.2.2.val.2.2=V.arguments.val.2.2 at endState
  rw [SignedPrep.visitsEquiv_outState,←endState,src.return_memory parts.2.2]
  exact tab.trans (sparse.trans (patch.trans ((Fin.ext frWord).trans (repWord.trans ctlWord))))

/-- Reader snapshot at the actual entry to the private calls. -/
theorem KeptToCalls.reader {A : StartupArena} {entries pins : ℕ} {boot pinMem owned calls : Memory w}
    (h : KeptToCalls A A.frame owned calls) (old : ReaderKept A entries pins boot pinMem owned)
    (packet : entries*w≤A.copied) (index : pins≤A.count) : ReaderKept A entries pins boot pinMem calls := by
  apply old.advance
  intro x hx
  exact h x (hx.below packet index) (hx.ne_field (by decide) (by decide)) (hx.ne_field (by decide) (by decide))

/-- The copied subtotal field and every boot operand used for its later
comparison are protected by the same stage-by-stage word equality. -/
theorem KeptToCalls.headerSeed {reserve axes groups cap width : ℕ} {A : StartupArena} {a : SignedTaskArena.Layout}
    {u : ℕ} {owned calls : Memory w}
    (p : TeamContraction.JointHeader.PositiveFields reserve axes groups cap a.cube.teams a.dim width)
    (h : KeptToCalls A (pub 0).val owned calls) (frame : (pub 0).val=A.frame)
    (size : A.header=TeamContraction.JointHeader.PositiveFields.width reserve axes groups cap a.cube.teams a.dim width) :
    let raw := rawAddress A reserve axes groups cap
    HeaderSeed a p pub raw u owned → HeaderSeed a p pub raw u calls := by
  intro raw old
  apply old.transfer
  intro x hx
  have read := frame ▸ hx
  obtain ⟨low,_,next⟩ := rawAddress_room a A size
  exact h x ((seedRead_before_pins a A size read).trans_le next)
    (frame ▸ headerSeedRead_other read low (j:=35) (by decide) (by decide))
    (frame ▸ headerSeedRead_other read low (j:=90) (by decide) (by decide))

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
