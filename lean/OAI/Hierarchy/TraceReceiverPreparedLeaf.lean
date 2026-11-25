import OAI.Hierarchy.TraceReceiverHeaderMount
import OAI.Hierarchy.TraceReceiverMaskLoop
import OAI.Hierarchy.TraceReceiverVirtualLeaf

namespace OAI
/-! # Executed receiver preparation of the local gates, table IDs and lane masks -/

namespace Hierarchy.TraceReceiverPreparedLeaf

open ThreeFlat Diagonal Diagonal.PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open RAM.PhysicalProcedure LaneCursor LaneCursor.RowLayout
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base q low fuel ell : ℕ}
variable (M : Machine (64*w) pc regs slots) (fit : NativeTrace.Fits M S base ((q+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w))
    (raw gateBase dict masks tmp : ℕ)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "traceDepth" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots traceDepth
local notation "templateWords" => TraceReceiverTemplate.words M fit hF st (FieldCode.ofCardLe hF) raw gateBase
local notation "n" => TraceReceiverTemplate.count G
local notation "off" => TraceReceiverMaskBanks.count (q+1) low
local notation "out" => TraceReceiverMaskLoop.output (q+1) low dict masks tmp
local notation "pack" => TraceReceiverTemplate.image gateBase templateWords
local notation "P" => TraceBitHeader.layout hF fit.width fit.labels base st fit.header fit.time regs slots fit.grid
local notation "N" => TraceBitHeader.network hF fit.width fit.labels base st fit.header fit.time regs slots traceDepth

section Header
variable (B : Block F) (axes ticks cap text : ℕ)
local notation "src" => 2+text+W*((GridStructuralHeader.directory (w:=w) B axes ticks cap).length+1)

/-- Direct execution on the chosen local bit tape, including the genuine fixed
header template and both dictionary and dense slot-offset initialization loops. -/
theorem run (textFit : text≤w^2)
    (self : Fin (w^2)→Bool) (index : Word W) (sel : Fin ell→Bool) (suffix : List Bool)
    (depth : traceDepth < W) (sr : dict+2^(q+1)*2^low≤tmp) (dr : masks+off≤tmp) (space : tmp+2*off < 2^W)
    (apart : gateBase+n ≤ src ∨ src+W*n ≤ gateBase) (dstFit : gateBase+n<2^W) (srcFit : src+W*n<2^W) :
    let args := GridStructuralHeader.parameters B axes ticks cap M fit hF st raw gateBase
    let head := GridReceiverHeader.header text textFit self index args sel
    let mem := TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape head suffix)
    ((PhysicalInputPhases.packing W src gateBase n).seq
      (TraceReceiverMaskLoop.program W (q+1) low dict masks tmp)).Exec mem (out (pack mem))
      (n*(5*W+6)+6+TraceReceiverMaskLoop.work W (q+1) low dict masks) := by
  exact Procedure.Exec.then (A:=PhysicalInputPhases.packing W src gateBase n)
    (B:=TraceReceiverMaskLoop.program W (q+1) low dict masks tmp)
    (TraceReceiverHeaderMount.run B axes ticks cap M fit hF st raw gateBase text textFit
      self index sel suffix apart dstFit srcFit)
    (TraceReceiverMaskLoop.run (q+1) low dict masks tmp _ depth sr dr space)

/-- On an already registered tick the publisher can install the true virtual
leaf and mask data after replay, retaining all earlier work below gateBase. -/
theorem run_after (textFit : text≤w^2) (self : Fin (w^2)→Bool) (index : Word W) (sel : Fin ell→Bool)
    (suffix : List Bool) (mem : Memory W) (safe : ℕ)
    (frame : ∀ z,z < safe → mem z=TickMountedPins.memory (w:=W) (TraceReceiverHeaderMount.tape
      (GridReceiverHeader.header text textFit self index (GridStructuralHeader.parameters B axes ticks cap M fit hF st raw gateBase) sel) suffix) z)
    (covered : src+W*n ≤ safe) (depth : traceDepth<W) (sr : dict+2^(q+1)*2^low≤tmp) (dr : masks+off≤tmp)
    (space : tmp+2*off<2^W) (apart : gateBase+n ≤ src ∨ src+W*n≤gateBase)
    (dstFit : gateBase+n<2^W) (srcFit : src+W*n<2^W) :
    ((PhysicalInputPhases.packing W src gateBase n).seq (TraceReceiverMaskLoop.program W (q+1) low dict masks tmp)).Exec
      mem (out (pack mem)) (n*(5*W+6)+6+TraceReceiverMaskLoop.work W (q+1) low dict masks) := by
  exact Procedure.Exec.then (A:=PhysicalInputPhases.packing W src gateBase n)
    (B:=TraceReceiverMaskLoop.program W (q+1) low dict masks tmp)
    (TraceReceiverHeaderMount.run_after B axes ticks cap M fit hF st raw gateBase text textFit
      self index sel suffix mem safe frame covered apart dstFit srcFit)
    (TraceReceiverMaskLoop.run (q+1) low dict masks tmp _ depth sr dr space)

end Header

/-- The immutable high preparation leaves every earlier input, navigation,
charge, forest and stage address below its fixed compact source bank untouched. -/
theorem below (mem : Memory W) (beforeD : gateBase≤dict) (beforeM : gateBase≤ masks)
    (sr : dict+2^(q+1)*2^low≤tmp) (dr : masks+off≤tmp) (space : tmp+2*off<2^W)
    {j : ℕ} (lowRead : j<gateBase) : out (pack mem) j=mem j := by
  rw [TraceReceiverMaskLoop.frame (q+1) low dict masks tmp (pack mem) j sr dr space
    (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
  exact TraceReceiverTemplate.image_outside gateBase templateWords mem (.inl lowRead)

/-- The compact gate and port records and IDs survive both writes. This is
sufficient for all virtual compiler loads and the once-per-gate metadata lookup. -/
theorem mounted (mem : Memory W) (beforeD : gateBase+n≤dict) (beforeM : gateBase+n≤ masks)
    (sr : dict+2^(q+1)*2^low≤tmp) (dr : masks+off≤tmp) (space : tmp+2*off < 2^W) :
    TraceReceiverVirtualLeaf.Mounted (q:=q) (low:=low) (S:=S) (f:=fuel) hF fit.width fit.labels
      base st regs slots raw gateBase hF (out (pack mem)) := by
  intro i hi
  rw [TraceReceiverMaskLoop.frame (q+1) low dict masks tmp (pack mem) (gateBase+i)
    sr dr space (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
  exact TraceReceiverTemplate.image_at gateBase templateWords mem ⟨i,hi⟩

/-- The preparation supplies the actual row evaluator using only the scalar
word-capacity and directory-placement inequalities. -/
theorem source (mem : Memory W) (beforeD : gateBase+n≤dict) (beforeM : gateBase+n≤ masks)
    (sr : dict+2^(q+1)*2^low≤tmp) (dr : masks+off≤tmp) (space : tmp+2*off < 2^W)
    (fits : gateBase+n < 2^W)
    (safe : ∀ (lane : Fin (2^traceDepth)) i, (TraceBitDescriptor.records (p:=pc) (r:=regs) (k:=slots) (d:=traceDepth)
      fit.width base S fuel i).Fits W lane.val) :
    TraceRawLookup.Sources N (FieldCode.ofCardLe hF)
      ⟨raw,(N).cells,gateBase+FixedTraceImage.count G+(G).cells⟩ (out (pack mem)) := by
  have localRoom := TraceReceiverTemplate.room G gateBase fits
    (TraceStaticRow.table_internal_le_cells hF fit.width fit.labels base fuel st regs slots traceDepth)
  exact TraceReceiverVirtualLeaf.source (q:=q) (low:=low) hF fit.width fit.labels base st
    fit.header fit.time regs slots raw gateBase hF _
    (mounted M fit hF st raw gateBase dict masks tmp mem beforeD beforeM sr dr space)
    localRoom.1 safe localRoom.2.1 localRoom.2.2.1 localRoom.2.2.2.1

theorem masks_read (mem : Memory W) (sr : dict+2^(q+1)*2^low≤tmp) (dr : masks+off≤tmp)
    (space : tmp+2*off < 2^W) (apart : dict+2^(q+1)*2^low≤ masks ∨ masks+off≤dict) :
    (∀ a : Occurrence N, (out (pack mem) (dict+((P).offset ((P).code a)).val)).val=((P).code a).val) ∧
    ∀ i, (out (pack mem) (masks+i.val)).val=((P).offset i).val :=
  TraceReceiverMaskLoop.readouts hF fit.width fit.labels base st fit.header fit.time regs slots fit.grid
    dict masks tmp (pack mem) sr dr space apart

end

end Hierarchy.TraceReceiverPreparedLeaf

end OAI
