import OAI.Computability.BorderVNP.RoutingISATypedHistoryBounds
import OAI.Computability.BorderVNP.CellPrivateTranslate
import OAI.Computability.BorderVNP.CellPacketGlobalClock

/-! # The native cell procedure on the sparse typed source packet

Routine zero now contains the actual finite decoder and compiler, followed by the
bounded-depth generator and signed evaluator. Its clock is measured on the original
sparse directory. The argument table, native choice histories, and signed value
refer to the same shared-memory computation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM CellMacro CellMacro.Generator CellSparse CellDispatch CompactMachine

/-- The fixed private driver on every raw typed cell input. -/
noncomputable def cellDriver : Fragment IO := CompactPacket.driver CellPrivate.translate 8 3

/-- The cost of the actual typed translator, physical packet read, generator and bytecode. -/
noncomputable def cellClock (w : ℕ) (c : CellInput) : ℕ :=
  2*CompactPacket.allowance w 8 c (CellPrivate.translateClock c.directory c.privateWires)

private theorem translation {w n : ℕ} (c : CellInput) (widths : c.directory.ProfileWidths)
    (clock : cellClock w c ≤ n^25) :
    ∃ t, CellPrivate.translate.Runs t (io (Packet.bits c.directory c.privateWires) c.external [])
        (io [] c.external (serialized 8 (c.directory.program c.privateWires))) ∧
      2*CompactPacket.allowance w 8 c t ≤ n^25 := by
  obtain ⟨t,ht,run⟩ := CellPrivate.translate_run c.directory c.privateWires c.external widths
  refine ⟨t,run,?_⟩
  unfold cellClock at clock
  simp only [CompactPacket.allowance_eq] at clock ⊢
  omega

/-- The real sparse packet machine contracts all internal signed choices, including
zero-weight halts, for the actual supplied external wire assignment. -/
theorem cell_value {w n : ℕ} (c : CellInput) (hw : 0 < w) (widths : c.directory.ProfileWidths)
    (clock : cellClock w c ≤ n^25) :
    ∑ o ∈ choices cellDriver n (CompactFrame.pack w (Packet.input c.directory c.privateWires c.external)),
      o.2.value = c.weight := by
  obtain ⟨t,run,ht⟩ := translation c widths clock
  exact CompactPacket.typed_cell_sum CellPrivate.translate c.directory c.privateWires c.external hw
    (c.directory.program_fitsDepth _) run ht

/-- Concrete packed-row witness for use by the subsequent weighted continuation
on the live, prepared memory. No abstract translator is supplied to this result. -/
theorem concretePackedRows {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} {cells : ℕ → CellInput} (hw : 0 < w)
    (placed : PlacedRows pub m tasks count n cells) (layout : Allocated w table count tasks)
    (room : ∀ j < count, (tasks j).cell.Room w) (control : ControlLayout pub m tasks count)
    (privateData : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      (cells i).directory.ProfileWidths ∧ cellClock w (cells i) ≤ n^25) :
    CompactMachine.PackedRows (Frame.ofMemory pub m) (written m tasks count) cellDriver n
      (fun i => Packet.input (cells i).directory (cells i).privateWires (cells i).external)
      (fun i => (cells i).stmt.expand []) :=
  packedRows CellPrivate.translate hw placed layout room control
    (fun i _ _ => (cells i).directory.program_fitsDepth _)
    (fun i hi own => translation (cells i) (privateData i hi own).1 (privateData i hi own).2)

/-- Native path sum and resource bounds for the team's batch of physically prepared
cell packets, with the real fixed private translator installed in the table. -/
theorem native_team_value {w table count n : ℕ} (pub : Arg → Word w) (s : Bank w) (m : Memory w)
    (tasks : ℕ → Task) (cells : ℕ → CellInput) (routines : TeamOpcode.Macros w 8)
    (frame : (pub 0).val+90 < 2^w) (width : (m ((pub 0).val+30)).val=w)
    (base : (m ((pub 0).val+89)).val=table) (len : (m ((pub 0).val+90)).val=count)
    (space : table+7*count ≤ 2^w) (layout : Allocated w table count tasks)
    (source : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m)
    (room : ∀ i < count, (tasks i).callRow+2 < 2^w ∧ (tasks i).cell.Room w)
    (control : ControlLayout pub m tasks count) (placed : PlacedRows pub m tasks count n cells)
    (directory : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (privateData : ∀ i < (Frame.ofMemory pub m).count,
      (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      (cells i).directory.ProfileWidths ∧ cellClock w (cells i) ≤ n^25) :
    let mac := install cellDriver n routines
    let f := Frame.ofMemory pub m
    let mt := written m tasks count
    ∃ pre t, Runs pub mac entry s m pre t mt ∧
      traceCost pre ≤ loadDirectory.slots+setup.slots+(∑ j ∈ Finset.range count, rowCharge (fun k => (tasks k).cell.cost w) j)+1 ∧
      let paths := CompactBatch.preparedHistories pre f pub mt (choices cellDriver n)
      (∀ bits es, TeamRAM.execute (runCells.program.fetch pub mac) ⟨0,s⟩ m bits = some es ↔
        es ∈ paths ∧ es.map TeamRAM.Event.choices = bits) ∧
      (∀ es ∈ paths, TeamContraction.Within (traceCost pre + (17+7*f.count+4*(f.ownedRows mt 0 f.count).length +
        ∑ j ∈ Finset.range count, ((tasks j).cell.burst w).length)) (TeamScales.width n (1/2)) (n^25) es) ∧
      ∑ es ∈ paths, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
        ((f.ownedRows m 0 f.count).map (fun i => (cells i).weight)).prod := by
  obtain ⟨pre,t,prep,cost,accept,val⟩ := team_sum (d:=8) (h:=3) pub s m tasks cells CellPrivate.translate routines
    frame width base len space layout source room control placed directory
    (fun i _ _ => (cells i).directory.program_fitsDepth _)
    (fun i hi own => translation (cells i) (privateData i hi own).1 (privateData i hi own).2)
  exact ⟨pre,t,prep,cost,accept,prepared_within cellDriver routines placed layout (fun i hi => (room i hi).2) control prep,val⟩

open Filter TeamScales

/-- At one uniform small exponent in the batch scale, the cap and clock hypotheses
for the concrete native routine follow from the stated cell sizes and the measured
running time of its deterministic typed translator. -/
theorem eventually_cell_resources (A B j : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
      ∀ c : CellInput, c.external.length ≤ E →
      c.directory.StaticBounds A M → c.directory.CompactFields c.privateWires (4*(M+E+1)^3) →
      c.directory.records.length ≤ 4*(M+E+1)^3 → c.directory.reportedCounts.length ≤ 4*(M+E+1)^3 →
      Packet.storedMass c.directory ≤ A*(M+1)^2 →
      (∀ v ∈ Packet.words c.directory c.privateWires, v.size ≤ B*(logWidth r n+1)^j) →
      CellPrivate.translateClock c.directory c.privateWires ≤ B*(M+E+1)^96*(logWidth r n+1)^j →
      (CompactFrame.pack w (Packet.input c.directory c.privateWires c.external)).length ≤ width n (1/2) ∧
      cellClock w c ≤ n^25 := by
  obtain ⟨ω,hω,h⟩ := CompactPacket.eventually_global_clock A B j
  refine ⟨ω,hω,?_⟩
  filter_upwards [h] with n hn
  intro r M E w hr hrω hM hE hw hwn c hExt hStatic hFields hRows hReports hMass hRaw hCost
  exact hn r M E w c.privateWires (CellPrivate.translateClock c.directory c.privateWires) hr hrω hM hE hw hwn
    c.directory c.external hExt hStatic hFields hRows hReports hMass hRaw hCost

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
