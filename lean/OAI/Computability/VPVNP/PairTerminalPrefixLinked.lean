import OAI.Computability.VPVNP.PairTerminalPrefixLayout
import OAI.Computability.VPVNP.PairTerminalStageReverse

/-!
# The first two stages of the linked terminal pair program

The bootstrap runs directly on the calendar's physical output memory. Its
accepting exit switches the controller to the prefix worker and resets the
saved ordinal. The prefix worker's own reads avoid those two control words.
Consequently its physical calls compute the same offsets, total width and
role displacement as the standalone final-state scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix.Linked

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords TerminalLink
open scoped Fin.CommRing
open LiveProgram (PairTable)

variable {w a g : ℕ}

/-- Package the terminal bootstrap instructions as a pair worker for the given descriptor shape
and record limit. -/
abbrev bootstrapWorker (F : DescriptorSpace.Shape) (limit : ℕ) : PairTable :=
  ⟨_, _, TerminalBootstrap.table F limit⟩

/-- The linked pair worker that visits final arcs and publishes their exclusive width prefixes. -/
abbrev prefixWorker : PairTable := ⟨_, _, Worker.table⟩

/-- External memory after replaying the wrapped initial bootstrap report at the pair's terminal
header. -/
def bootMemory (pub : Fin 11 → Word w) (m : Memory w) (raw : Report w) : Memory w :=
  after m (report (header pub) .initial raw).events

/-- No read-transport condition is required at the initial call, which runs
on exactly the input memory of the physical terminal table. -/
theorem initial_oneShot (workers : Stage → PairTable) (pub : Fin 11 → Word w)
    (f cap : ℕ) (m : Memory w) (raw : Report w) (fit : 32 ≤ 2 ^ w) (room : f + 30 ≤ cap)
    (call : execute (source workers Stage.bootstrap pub) f
      ((source workers Stage.bootstrap pub).start 0) m [] = some raw) (halt : raw.result = none) :
    StageRun workers pub cap .initial m m [[]] [raw] := by
  let e : Entry w := .initial
  have nextEntry : e.follow raw = some (.resume Stage.prefixRows 0) := by
    rw [Entry.follow, halt]
    rfl
  have nextHandoff : handoff (w := w) e.stage = some (.resume Stage.prefixRows 0) := rfl
  have physical := call_of_room workers pub cap e m [] (by omega) trivial f raw call room
  constructor
  · change runSegment (program workers pub) cap (some e.marker) m [[]] =
      some [report (header pub) e raw]
    simp only [runSegment, physical, Option.map_some]
  · change (report (header pub) e raw).result = (handoff e.stage).map Entry.marker
    rw [report_result, nextEntry, nextHandoff]
  · simp only [stageReports, eventLog, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change SourceTransport.Agree (workerCell (header pub)) (after m raw.events)
      (after m (report (header pub) e raw).events)
    rw [report_after, show e.stage = Stage.bootstrap from rfl, halt]
    intro j hj
    change after m raw.events j = writeMemory (writeMemory (after m raw.events)
      (header pub) (tagWord w Stage.prefixRows)) (header pub + 31) 0 j
    simp only [writeMemory, ite_eq_right hj.1, ite_eq_right hj.2]
  · intro t ht
    change handoff e.stage = some t at ht
    rw [nextHandoff] at ht
    obtain rfl := Option.some.inj ht
    simpa only [stageReports, eventLog, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using next_valid (header pub) e _ raw m fit nextEntry

/-- Standalone final-state reports run at the physical prefix entry, where only
the stage and saved ordinal may differ from their standalone values. -/
theorem prefix_stage (workers : Stage → PairTable) (bank : workers Stage.prefixRows = prefixWorker)
    (pub : Fin 11 → Word w) (cap : ℕ) (X : State a g) (T : IncidenceDirectory w)
    (base : Word w) (src phy : Memory w) (rs : List (Report w))
    (scan : Segment.Run pub X T base src rs) (room : 60 ≤ cap)
    (fits : (header pub).val + 32 ≤ 2 ^ w) (widths : T.width.val + arcCount X ≤ (header pub).val)
    (starts : base.val + arcCount X ≤ (header pub).val)
    (valid : (Entry.resume Stage.prefixRows (0 : Word w)).Valid (header pub) phy)
    (agree : SourceTransport.Agree (workerCell (header pub)) src phy) :
    StageRun workers pub cap (.resume Stage.prefixRows 0) src phy
      (List.replicate (arcCount X + 1) []) rs := by
  apply closed_stage_run workers pub 30 cap _ src phy _ rs (by omega) room valid agree
    (scan.controller_frame fits widths starts).1
  · change runSegment ((workers Stage.prefixRows).table.instantiate w pub).program 30
      (some 0) src _ = some rs
    rw [bank]
    exact scan.native
  · exact scan.halt

/-- Both physical stage runs and their underlying source computations. -/
structure Start (workers : Stage → PairTable) (pub : Fin 11 → Word w) (cap f : ℕ)
    (X : State a g) (T : IncidenceDirectory w) (base : Word w) (m : Memory w)
    (raw : Report w) (rs : List (Report w)) : Prop where
  bootCall : execute (source workers Stage.bootstrap pub) f
    ((source workers Stage.bootstrap pub).start 0) m [] = some raw
  bootHalt : raw.result = none
  rawScan : Segment.Run pub X T base (after m raw.events) rs
  prefixBank : workers Stage.prefixRows = prefixWorker
  reads : SourceTransport.Reads (workerCell (header pub)) (eventLog rs)
  boot : StageRun workers pub cap .initial m m [[]] [raw]
  scan : StageRun workers pub cap (.resume Stage.prefixRows 0) (after m raw.events)
    (bootMemory pub m raw) (List.replicate (arcCount X + 1) []) rs

/-- Compose the actual two workers into the terminal controller. -/
theorem start (workers : Stage → PairTable) (bank : workers Stage.prefixRows = prefixWorker)
    (pub : Fin 11 → Word w) (cap f : ℕ) (X : State a g) (T : IncidenceDirectory w)
    (base : Word w) (m : Memory w) (raw : Report w) (rs : List (Report w))
    (bootCall : execute (source workers Stage.bootstrap pub) f
      ((source workers Stage.bootstrap pub).start 0) m [] = some raw) (bootHalt : raw.result = none)
    (scan : Segment.Run pub X T base (after m raw.events) rs) (clock : f + 30 ≤ cap)
    (room : 60 ≤ cap) (fits : (header pub).val + 32 ≤ 2 ^ w)
    (widths : T.width.val + arcCount X ≤ (header pub).val)
    (starts : base.val + arcCount X ≤ (header pub).val) :
    Start workers pub cap f X T base m raw rs := by
  have boot := initial_oneShot workers pub f cap m raw (by omega) clock bootCall bootHalt
  have valid : (Entry.resume Stage.prefixRows (0 : Word w)).Valid (header pub)
      (bootMemory pub m raw) := by
    simpa only [bootMemory, stageReports, eventLog, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
      using boot.valid (.resume Stage.prefixRows 0) rfl
  have agree : SourceTransport.Agree (workerCell (header pub)) (after m raw.events)
      (bootMemory pub m raw) := by
    simpa only [bootMemory, stageReports, eventLog, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
      using boot.agree
  exact ⟨bootCall, bootHalt, scan, bank, (scan.controller_frame fits widths starts).1, boot,
    prefix_stage workers bank pub cap X T base (after m raw.events) (bootMemory pub m raw) rs
      scan room fits widths starts valid agree⟩

open DescriptorSpace

/-- The bootstrap and prefix stage of the actual packed terminal workspace.
The physical memory on exit agrees with the raw scan outside the controller's
phase and saved-state cells, and is a valid entry to traversal-row construction. -/
theorem run_packed (workers : Stage → PairTable) (L : Layout) (last : Fin L.levels)
    (tab : Fin L.shape.tables) (A : TerminalBootstrap.Header L last) (limit r cap : ℕ)
    (bank₀ : workers Stage.bootstrap = bootstrapWorker L.shape limit)
    (bank₁ : workers Stage.prefixRows = prefixWorker) (pub : Fin 11 → Word w)
    (m : Memory w) (X : State a g) (ready : TerminalBootstrap.Ready L last A pub m)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ L.base + 2 ^ r * 2 ^ r)
    (room : L.base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (above : endAddress L ≤ TerminalBootstrap.address L.base r)
    (nslots : A.sites * A.degree = arcCount X)
    (wh : A.widthHead = incidenceBase L last (arcCount X) 5)
    (sh : A.prefixBase = tableBase L last tab) (slots : arcCount X ≤ slotCapacity L)
    (cells : arcCount X ≤ tableWords L) (totalFit : X.totalWidth < 2 ^ w)
    (incidence : (packedIncidence L w last (arcCount X)).ActualColumns X m)
    (clock₀ : TerminalBootstrap.cost L.shape limit + 1 + 30 ≤ cap) (clock₁ : 60 ≤ cap) :
    let raw := TerminalBootstrap.report L.shape limit pub 0 m
    let T := packedIncidence L w last (arcCount X)
    let f := TerminalBootstrap.cost L.shape limit + 1
    ∃ rs, Start workers pub cap f X T (tableBase L last tab) m raw rs ∧
      after (after m raw.events) (eventLog rs) (header pub + 14).val =
        ((A.rowWords limit + X.totalWidth : ℕ) : Word w) := by
  let raw := TerminalBootstrap.report L.shape limit pub 0 m
  let T := packedIncidence L w last (arcCount X)
  let f := TerminalBootstrap.cost L.shape limit + 1
  obtain ⟨boot, rs, scan, role⟩ := run_after_bootstrap L last tab A limit r pub 0 m X
    ready exp hr reserve room above nslots wh sh slots cells totalFit incidence
  have call : execute (source workers Stage.bootstrap pub) f
      ((source workers Stage.bootstrap pub).start 0) m [] = some raw := by
    unfold source
    rw [bank₀]
    exact boot
  have hv := header_val L pub r ready.workspace exp hr reserve room
  have fits : (header pub).val + 32 ≤ 2 ^ w := by
    rw [hv, TerminalBootstrap.address]
    omega
  have ht : tableBase L last tab + arcCount X ≤ (header pub).val :=
    (Nat.add_le_add_left cells _).trans ((tableEnd_le_nextLevel L last tab).trans
      ((levelStart_mono L last.isLt).trans (above.trans_eq hv.symm)))
  have baseVal : ((tableBase L last tab : ℕ) : Word w).val = tableBase L last tab :=
    Nat.mod_eq_of_lt (by omega)
  have widths : T.width.val + arcCount X ≤ (header pub).val :=
    (prefix_bounds L (w := w) last tab (arcCount X) (header pub).val slots cells
      (above.trans_eq hv.symm) (by omega)).1.trans
      ((Nat.le_add_right _ _).trans ht)
  have starts : ((tableBase L last tab : ℕ) : Word w).val + arcCount X ≤ (header pub).val := by
    rw [baseVal]
    exact ht
  exact ⟨rs, start workers bank₁ pub cap f X T _ m raw rs call rfl scan clock₀ clock₁ fits
    widths starts, role⟩

variable {workers : Stage → PairTable} {pub : Fin 11 → Word w} {cap f : ℕ}
variable {X : State a g} {T : IncidenceDirectory w} {base : Word w}
variable {m : Memory w} {raw : Report w} {rs : List (Report w)}

/-- The exact physical state after both deterministic stages. -/
def prefixMemory (pub : Fin 11 → Word w) (m : Memory w) (raw : Report w)
    (rs : List (Report w)) : Memory w :=
  after (bootMemory pub m raw)
    (eventLog (stageReports (header pub) (.resume Stage.prefixRows 0) rs))

theorem Start.handoff_rows (s : Start workers pub cap f X T base m raw rs) :
    SourceTransport.Agree (workerCell (header pub)) (after (after m raw.events) (eventLog rs))
        (prefixMemory pub m raw rs) ∧
      (Entry.resume Stage.traversalRows (0 : Word w)).Valid (header pub)
        (prefixMemory pub m raw rs) :=
  ⟨s.scan.agree, s.scan.valid _ rfl⟩

/-- The two canonical forward phases can be inserted directly in a five-stage trace. -/
theorem Start.phases (s : Start workers pub cap f X T base m raw rs)
    (clock₀ : f + 30 ≤ cap) (clock₁ : 60 ≤ cap) :
    Phase workers pub cap .initial m [[]] [(.initial, raw)] (bootMemory pub m raw) ∧
      Phase workers pub cap (.resume Stage.prefixRows 0) (bootMemory pub m raw)
        (List.replicate (arcCount X + 1) []) (stageLogs (.resume Stage.prefixRows 0) rs)
        (prefixMemory pub m raw rs) := by
  refine ⟨initial_phase workers pub f cap m raw clock₀ s.bootCall s.bootHalt, ?_⟩
  have agree : SourceTransport.Agree (workerCell (header pub)) (after m raw.events)
      (bootMemory pub m raw) := by
    simpa only [bootMemory, stageReports, eventLog, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using s.boot.agree
  apply Phase.of_source_segment (workers := workers) (e := .resume Stage.prefixRows 0)
    (f := 30) clock₁ agree s.reads _ s.rawScan.halt
  change runSegment ((workers Stage.prefixRows).table.instantiate w pub).program 30
    (some 0) (after m raw.events) _ = some rs
  rw [s.prefixBank]
  exact s.rawScan.native

/-- An arbitrary accepted trace has the canonical empty tapes, exact tagged
worker reports, and exact physical output memory at both early stage boundaries. -/
theorem Start.force (s : Start workers pub cap f X T base m raw rs)
    (t : FiveTrace workers pub cap m) :
    t.bootstrap.choices = [[]] ∧ t.bootstrap.logs = [(.initial, raw)] ∧
      t.bootstrap.memory = bootMemory pub m raw ∧
      t.prefixRows.choices = List.replicate (arcCount X + 1) [] ∧
      t.prefixRows.logs = stageLogs (.resume Stage.prefixRows 0) rs ∧
      t.prefixRows.memory = prefixMemory pub m raw rs := by
  apply t.canonical_start s.bootCall s.bootHalt (g := 30) _ s.rawScan.halt s.reads
  change runSegment ((workers Stage.prefixRows).table.instantiate w pub).program 30
    (some 0) (after m raw.events) _ = some rs
  rw [s.prefixBank]
  exact s.rawScan.native

/-- Read the exclusive total, the role displacement, and every arc offset
from the physical memory that is actually handed to the traversal-row stage. -/
theorem Start.physical_readback (s : Start workers pub cap f X T base m raw rs)
    (fits : (header pub).val + 32 ≤ 2 ^ w) (below : base.val + arcCount X ≤ (header pub).val) :
    let out := prefixMemory pub m raw rs
    (out (header pub + 12).val).val = X.totalWidth ∧
      out (header pub + 14).val = Segment.roleValue pub X (after m raw.events) ∧
      ∀ i : Fin (arcCount X), (out (base.val + i.val)).val = EndpointBits.offset (width X) i := by
  have pos (j : ℕ) (hj : j < 32) :
      (header pub + (j : Word w)).val = (header pub).val + j := by
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : j < 2 ^ w),
      Nat.mod_eq_of_lt (by omega)]
  have saved : (header pub + 31).val = (header pub).val + 31 := pos 31 (by decide)
  have away (j : ℕ) (hj : 0 < j) (hs : j < 31) : workerCell (header pub)
      (header pub + (j : Word w)).val := by
    unfold workerCell
    rw [pos j (by omega), saved]
    omega
  have agree := s.handoff_rows.1
  refine ⟨(congrArg Fin.val (agree _ (away 12 (by decide) (by decide))).symm).trans
    s.rawScan.stored.total, (agree _ (away 14 (by decide) (by decide))).symm.trans s.rawScan.role,
    fun i => ?_⟩
  have idx : workerCell (header pub) (base.val + i.val) := by
    have hi := i.isLt
    unfold workerCell
    rw [saved]
    omega
  exact (congrArg Fin.val (agree _ idx).symm).trans (s.rawScan.stored.start i)

end PairSimulation.TerminalPrefix.Linked

end VPVNP
end Computability
end OAI
