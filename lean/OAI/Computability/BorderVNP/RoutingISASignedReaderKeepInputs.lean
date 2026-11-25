import OAI.Computability.BorderVNP.RoutingISASignedReaderKeep
import OAI.Computability.BorderVNP.RoutingISACubeArenaGuardBoot
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTraversalLow
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSuffix
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedTaskSource
import OAI.Computability.BorderVNP.DiagonalTallyCallReadback

/-! # Actual signed evaluator preparation preserves the chosen reader's inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ReaderKept

open VPVNP.BurstRAM TeamContraction.ProcessorSlots
open BorderVNP.Cube BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRows
open BorderVNP.FiniteEvaluator DiagonalTallyCellReports DiagonalTallyAllocation
open CellPacket.Supplement.Batch

variable {w : ℕ} {A : StartupArena} {entries pins : ℕ} {boot pinMem : Memory w}

/-- A startup word below both placement arrays and the emitted directory survives every epoch and publication, except the true row count. -/
theorem afterEpochs_word {o : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r t : Bank w}
    {fresh dest clock : ℕ} {out : Fin o → ℕ} {es geom slotted}
    (geometry : PackedHistoryCircuit.GeometryReturn pub mac r pinMem fresh dest clock out es t geom)
    (l : PrivatePlacement.Layout) (image : l.Image (readings geom) l.entries (readings slotted))
    (base : ℕ) (rows : List Packing.Directory.Row) (floor x : ℕ)
    (low : floor ≤ fresh ∧ floor ≤ l.raw ∧ floor ≤ l.scratch ∧ floor ≤ base)
    (lo : x<floor) (ct : x≠(pub 0).val+9) :
    Packing.Directory.ISA.publish slotted (pub 0).val base rows x=pinMem x := by
  rw [Packing.Directory.ISA.publish,Function.update_of_ne ct,Packing.Directory.ISA.putWords_outside _ _ _ _ (.inl (by omega))]
  exact (Fin.ext (image.outside x (fun _ _ => by omega) (.inl (by omega)))).trans (geometry.preserved _ (by omega))

/-- The real epoch decoder, private-slot writer and raw directory publisher act
above the boot, gate and index banks except for the published raw row count. -/
theorem afterEpochs {o : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r t : Bank w}
    {fresh dest clock : ℕ} {out : Fin o → ℕ} {es geom slotted}
    (geometry : PackedHistoryCircuit.GeometryReturn pub mac r pinMem fresh dest clock out es t geom)
    (l : PrivatePlacement.Layout) (image : l.Image (readings geom) l.entries (readings slotted))
    (base : ℕ) (rows : List Packing.Directory.Row) (start : ReaderKept A entries pins boot pinMem pinMem)
    (frame : (pub 0).val=A.frame) (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (low : A.next ≤ fresh ∧ A.next ≤ l.raw ∧ A.next ≤ l.scratch ∧ A.next ≤ base) :
    ReaderKept A entries pins boot pinMem (Packing.Directory.ISA.publish slotted (pub 0).val base rows) := by
  apply start.advance
  intro x hx
  exact afterEpochs_word geometry l image base rows A.next x low (hx.below packet index)
    (frame ▸ hx.ne_field (by decide) (by decide))

/-- The complete checked public route keeps every addressed low word except the published transmission count. -/
theorem afterRoute_word (a : CubeArena.Layout) (pub : Arg → Word w) (emit : Transmission.DataWriter.Layout)
    {g : SharedRows.Layout} {start preData preRoute routed : Memory w} {scheduled : ℕ → ℕ}
    (ctrl : ℕ) (axis : Fin (a.n+1)) (group : ∀ x < a.header.header, scheduled x=readings start x)
    (pair : PairDirectory.Image (a.pairWriter (pub 0).val)
      ((a.cellWriter (pub 0).val ctrl axis).written scheduled a.cells)
      (a.pairWriter (pub 0).val).count (readings preData))
    (shared : g.Emitted (readings (Transmission.DataWriter.publish emit pub preData)) (readings preRoute))
    (gf : g.frame=(pub 0).val) (gr : g.records=emit.output) (ar : emit.output=a.records)
    (path : ∀ x < a.records, routed x=preRoute x)
    (x : ℕ) (under : x<a.header.header) (count : x≠(pub 0).val+13) : routed x=start x := by
  obtain ⟨hd,_,_,_,_,_,pw,gw,gt,ot,op,ph,hr⟩ := a.group_order
  rw [path _ (by omega)]
  apply Fin.ext
  exact (CubeArena.emitted_before_records emit pub preData shared gf gr x (by omega) count).trans
    ((pair.outside x (.inl (by change x<a.pairDirectory; omega))).trans
      (((a.cellWriter _ ctrl axis).written_outside scheduled a.cells x (.inl (by change x<a.hostDirectory; omega))).trans
        (group x under)))

/-- Low-memory readback of the actual checked public prefix, the installed cell
banks, pair-directory writer, both row emitters and complete returning route. -/
theorem afterRoute (a : CubeArena.Layout) (pub : Arg → Word w) (emit : Transmission.DataWriter.Layout)
    {g : SharedRows.Layout} {start preData preRoute routed : Memory w} {scheduled : ℕ → ℕ}
    (ctrl : ℕ) (axis : Fin (a.n+1)) (group : ∀ x < a.header.header, scheduled x=readings start x)
    (pair : PairDirectory.Image (a.pairWriter (pub 0).val)
      ((a.cellWriter (pub 0).val ctrl axis).written scheduled a.cells)
      (a.pairWriter (pub 0).val).count (readings preData))
    (shared : g.Emitted (readings (Transmission.DataWriter.publish emit pub preData)) (readings preRoute))
    (gf : g.frame=(pub 0).val) (gr : g.records=emit.output) (ar : emit.output=a.records)
    (path : ∀ x < a.records, routed x=preRoute x)
    (old : ReaderKept A entries pins boot pinMem start)
    (frame : (pub 0).val=A.frame) (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (floor : A.next ≤ a.header.header) : ReaderKept A entries pins boot pinMem routed := by
  apply old.advance
  intro x hx
  exact afterRoute_word a pub emit ctrl axis group pair shared gf gr ar path x
    ((hx.below packet index).trans_le floor) (frame ▸ hx.ne_field (by decide) (by decide))

/-- An address below all four control and host outputs survives every actual opening-suffix run, except the owned cell count. -/
theorem afterControls_word (H : OpenSuffix.Inputs) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r m es t mt} (ready : OpenSuffix.Ready H (pub 0).val (readings m) w)
    (run : Runs pub mac OpenSuffix.code r m es t mt) (floor x : ℕ) (low : x<floor)
    (away : x≠(pub 0).val+90)
    (host : let l := HostScatter.Layout.fromFrame (pub 0).val (readings m)
      ∀ i < l.count, ∀ side, l.Owned (readings m) i side → floor ≤ l.dest (readings m) i side)
    (tables : OpenSuffix.AfterDeck H floor) : mt x=m x := by
  have image : readings mt=H.image (pub 0).val (readings m) := ((OpenSuffix.run H ready).sound run).2
  apply Fin.ext
  change readings mt x=readings m x
  rw [image]
  apply OpenSuffix.image_outside
  · dsimp only
    intro i hi side own; exact .inl (low.trans_le (host i hi side own))
  · exact .inl (low.trans_le tables.ranges)
  · exact .inl (low.trans_le tables.bundles)
  · have four := tables.four
    have six := tables.six
    have frameAt := ready.controlBase
    unfold CellControlRows.Layout.outputs
    omega

/-- The four output tables of the padding, host cable, bundle and control block
precede the report scan. The true cable destination of each owned endpoint is
above the reader's inputs. Only field 90 is published in the old frame. -/
theorem afterControls (H : OpenSuffix.Inputs) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r m es t mt} (ready : OpenSuffix.Ready H (pub 0).val (readings m) w)
    (run : Runs pub mac OpenSuffix.code r m es t mt) (old : ReaderKept A entries pins boot pinMem m)
    (frame : (pub 0).val=A.frame) (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (host : let l := HostScatter.Layout.fromFrame (pub 0).val (readings m)
      ∀ i < l.count, ∀ side, l.Owned (readings m) i side → A.next ≤ l.dest (readings m) i side)
    (tables : OpenSuffix.AfterDeck H A.next) : ReaderKept A entries pins boot pinMem mt := by
  apply old.advance
  intro x hx
  exact afterControls_word H ready run A.next x (hx.below packet index)
    (frame ▸ hx.ne_field (by decide) (by decide)) host tables

/-- Every word below the receiving cells remains available after the true report guesses, except the sparse descriptor count. -/
theorem afterReports_word {pre : BeforeTasks} {post : AfterTasks} {bank : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {m mt : Memory w}
    (alloc : ReportAllocation pre post bank l cs q) (image : readings mt=applyWrites (readings m) (prepareWrites cs q))
    (x : ℕ) (lower : x<bank.bankStart) (ne : x≠l.frame+35) : mt x=m x := by
  apply Fin.ext
  change readings mt x=readings m x
  rw [image]
  apply writes_outside
  intro store hs
  rw [prepareWrites,List.mem_append] at hs
  rcases hs with hc | hc
  · exact Or.inl (lower.trans_le (alloc.aboveBankStart store hc))
  · have eq := List.mem_singleton.mp hc
    subst store
    change x < l.frame+35 ∨ l.frame+35+1 ≤ x
    omega

/-- The actual report writes occupy each assigned cell or a later report bank;
their final one-word publication is at frame field 35. -/
theorem afterReports {pre : BeforeTasks} {post : AfterTasks} {bank : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {m mt : Memory w}
    (alloc : ReportAllocation pre post bank l cs q) (image : readings mt=applyWrites (readings m) (prepareWrites cs q))
    (old : ReaderKept A entries pins boot pinMem m) (frame : l.frame=A.frame)
    (packet : entries*w ≤ A.copied) (index : pins ≤ A.count) (space : A.next ≤ bank.bankStart) :
    ReaderKept A entries pins boot pinMem mt := by
  apply old.advance
  intro x hx
  exact afterReports_word alloc image x ((hx.below packet index).trans_le space)
    (frame ▸ hx.ne_field (k:=35) (by decide) (by decide))

end RoutingISA.ReaderKept

end BorderVNP
end Computability
end OAI
