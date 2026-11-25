import OAI.Computability.BorderVNP.RoutingISATypedBatchEntry
import OAI.Computability.BorderVNP.RoutingISACompactPrepared
import OAI.Computability.BorderVNP.RoutingISATypedDirectory
import OAI.Computability.BorderVNP.CellPacketTypedInitializer

/-!
# Native signed value of the typed cell-preparation and dispatch stage

The physical task table names the public and delivered source intervals. The team
constructs every packet, writes the returned pointer and length, and only then calls
its private machine on those words. The canonical trace prefix is unique and positive.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM CellDispatch CellMacro.Generator CellSparse
open CompactMachine (CellInput)

/-- This stage physically prepares the typed packets and executes the owner-indexed calls. -/
def runCells : Code := .seq entry callOwnedCells

/-- All writes avoid the frame fields and the owner column of every call row. -/
structure ControlLayout {w : ℕ} (pub : Arg → Word w) (m : Memory w) (tasks : ℕ → Task)
    (count : ℕ) : Prop where
  /-- The team number and both call-table fields survive preparation. -/
  frame : ∀ j < count, ∀ k ∈ [0,14,15], (tasks j).Outside w ((pub 0).val+k)
  /-- Every recorded cell owner survives preparation. -/
  owners : ∀ j < count, ∀ i < (Frame.ofMemory pub m).count, (tasks j).Outside w ((Frame.ofMemory pub m).address i)

/-- The canonical directory still has its original team, base, count and owners. -/
theorem ControlLayout.survives {w : ℕ} {pub : Arg → Word w} {m : Memory w} {tasks : ℕ → Task} {count : ℕ}
    (h : ControlLayout pub m tasks count) :
    Frame.ofMemory pub (written m tasks count) = Frame.ofMemory pub m ∧
    ∀ i < (Frame.ofMemory pub m).count,
      written m tasks count ((Frame.ofMemory pub m).address i) = m ((Frame.ofMemory pub m).address i) := by
  have field (k : ℕ) (hk : k ∈ [0,14,15]) : written m tasks count ((pub 0).val+k) = m ((pub 0).val+k) :=
    preserve m tasks (i := 0) (Nat.zero_le _) _ (fun j _ hj => h.frame j hj k hk)
  constructor
  · simp only [Frame.ofMemory,show written m tasks count (pub 0).val = m (pub 0).val from field 0 (by simp),
      field 14 (by simp),field 15 (by simp)]
  · intro i hi
    exact preserve m tasks (i := 0) (Nat.zero_le _) _ (fun j _ hj => h.owners j hj i hi)

/-- Real pointer publication plus the compact argument relation for every owned cell. -/
structure PlacedRows {w : ℕ} (pub : Arg → Word w) (m : Memory w) (tasks : ℕ → Task)
    (count n : ℕ) (cells : ℕ → CellInput) : Prop where
  /-- An owned call row receives one task's actual pointer and word count. -/
  task : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val = (Frame.ofMemory pub m).team →
    ∃ j < count, (tasks j).callRow = (Frame.ofMemory pub m).address i ∧
      (tasks j).cell.payload = Packet.input (cells i).directory (cells i).privateWires (cells i).external
  /-- Each actual task obeys the square-root burst cap. -/
  cap : ∀ j < count, ((tasks j).cell.burst w).length ≤ TeamScales.width n (1/2)

/-- The generator's semantic input determined by a physically placed set of sources. -/
def cellInput {Site : Type} (p : CellPacket.Placed Site) : CellInput :=
  ⟨p.directory,p.privateWires,p.external⟩

/-- When the owned task rows name their corresponding placed sources, their packet
contents follow from the actual chunk plan, including the original opaque site boxes. -/
theorem PlacedRows.of_placed {Site : Type} {w count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} (placed : ℕ → CellPacket.Placed Site)
    (row : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      ∃ j < count, (tasks j).callRow = (Frame.ofMemory pub m).address i ∧ (tasks j).cell = (placed i).task)
    (cap : ∀ j < count, ((tasks j).cell.burst w).length ≤ TeamScales.width n (1/2)) :
    PlacedRows pub m tasks count n (fun i => cellInput (placed i)) := by
  refine ⟨?_,cap⟩
  intro i hi own
  obtain ⟨j,hj,address,task⟩ := row i hi own
  refine ⟨j,hj,address,?_⟩
  rw [task]
  exact (placed i).payload

/-- After all preparation tasks, every owned row points to its complete actual packet. -/
theorem PlacedRows.arguments {w table count n : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} {cells : ℕ → CellInput} (placed : PlacedRows pub m tasks count n cells)
    (layout : Allocated w table count tasks) (room : ∀ j < count, (tasks j).cell.Room w)
    (control : ControlLayout pub m tasks count) :
    let f := Frame.ofMemory pub m
    let mt := written m tasks count
    ∀ i < f.count, (mt (f.address i)).val = f.team →
      (mt (f.address i+1)).val + (mt (f.address i+2)).val ≤ 2^w ∧
      (mt (f.address i+2)).val ≤ TeamScales.width n (1/2) ∧
      TeamRAM.previous mt (f.burst mt i) =
        CompactFrame.pack w (Packet.input (cells i).directory (cells i).privateWires (cells i).external) := by
  intro f mt i hi own
  have owner := control.survives.2
  obtain ⟨j,hj,row,payload⟩ := placed.task i hi ((owner i hi) ▸ own)
  obtain ⟨ptr,num,read⟩ := layout.output_words m j hj (room j hj)
  rw [row] at ptr num read
  refine ⟨?_,?_,?_⟩
  · rw [ptr,num]; exact (room j hj).burstFit
  · rw [num]; exact placed.cap j hj
  · exact read.trans (congrArg (CompactFrame.pack w) payload)

/-- The full native machine witness for every owned row, in the final memory
written by the physical typed task batch. -/
theorem packedRows {w table count n d h : ℕ} {pub : Arg → Word w} {m : Memory w}
    {tasks : ℕ → Task} {cells : ℕ → CellInput} (translate : Fragment IO) (hw : 0 < w)
    (placed : PlacedRows pub m tasks count n cells) (layout : Allocated w table count tasks)
    (room : ∀ j < count, (tasks j).cell.Room w) (control : ControlLayout pub m tasks count)
    (depth : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      ((cells i).directory.program (cells i).privateWires).FitsDepth d h)
    (compiler : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      ∃ t, translate.Runs t (io (Packet.bits (cells i).directory (cells i).privateWires) (cells i).external [])
        (io [] (cells i).external (serialized d ((cells i).directory.program (cells i).privateWires))) ∧
        2*CompactPacket.allowance w d (cells i) t ≤ n^25) :
    CompactMachine.PackedRows (Frame.ofMemory pub m) (written m tasks count) (CompactPacket.driver translate d h) n
      (fun i => Packet.input (cells i).directory (cells i).privateWires (cells i).external)
      (fun i => (cells i).stmt.expand []) := by
  have args := placed.arguments layout room control
  have owners := control.survives.2
  exact CompactPacket.packedRows translate cells hw (fun i hi own => (args i hi own).1)
    (fun i hi own => (args i hi own).2.1) (fun i hi own => (args i hi own).2.2)
    (fun i hi own => depth i hi ((owners i hi) ▸ own)) (fun i hi own => compiler i hi ((owners i hi) ▸ own))

/-- Complete chronological executions of this fixed preparation and dispatch table sum
to the product over the team's actual assigned cells. The private translator is used
only through true machine runs on the corresponding typed metadata. -/
theorem team_sum {w table count n d h : ℕ} (pub : Arg → Word w) (s : Bank w) (m : Memory w)
    (tasks : ℕ → Task) (cells : ℕ → CellInput) (translate : Fragment IO) (routines : TeamOpcode.Macros w 8)
    (frame : (pub 0).val+90 < 2^w) (width : (m ((pub 0).val+30)).val=w)
    (base : (m ((pub 0).val+89)).val=table) (len : (m ((pub 0).val+90)).val=count)
    (space : table+7*count ≤ 2^w) (layout : Allocated w table count tasks)
    (source : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m)
    (room : ∀ i < count, (tasks i).callRow+2 < 2^w ∧ (tasks i).cell.Room w)
    (control : ControlLayout pub m tasks count) (placed : PlacedRows pub m tasks count n cells)
    (directory : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (depth : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      ((cells i).directory.program (cells i).privateWires).FitsDepth d h)
    (compiler : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      ∃ t, translate.Runs t (io (Packet.bits (cells i).directory (cells i).privateWires) (cells i).external [])
        (io [] (cells i).external (serialized d ((cells i).directory.program (cells i).privateWires))) ∧
        2*CompactPacket.allowance w d (cells i) t ≤ n^25) :
    let gen := CompactPacket.driver translate d h
    let mac := CompactMachine.install gen n routines
    let f := Frame.ofMemory pub m
    ∃ pre t, Runs pub mac entry s m pre t (written m tasks count) ∧
      traceCost pre ≤ loadDirectory.slots+setup.slots+(∑ j ∈ Finset.range count, rowCharge (fun k => (tasks k).cell.cost w) j)+1 ∧
      let paths := CompactBatch.preparedHistories pre f pub (written m tasks count) (CompactMachine.choices gen n)
      (∀ bits es, TeamRAM.execute (runCells.program.fetch pub mac) ⟨0,s⟩ m bits = some es ↔
        es ∈ paths ∧ es.map TeamRAM.Event.choices = bits) ∧
      ∑ es ∈ paths, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
        ((f.ownedRows m 0 f.count).map (fun i => (cells i).weight)).prod := by
  intro gen mac f
  let mt := written m tasks count
  obtain ⟨pre,t,prep,cost,_⟩ := entry_run pub mac s m tasks frame width base len space layout source room
  obtain ⟨ff,owner⟩ := control.survives
  change Frame.ofMemory pub mt = f at ff
  change ∀ i < f.count, mt (f.address i) = m (f.address i) at owner
  have args := placed.arguments layout (fun i hi => (room i hi).2) control
  refine ⟨pre,t,prep,cost,?_,?_⟩
  · intro bits es
    have endRoom : (Frame.ofMemory pub mt).base + 3*(Frame.ofMemory pub mt).count ≤ 2^w := by
      rw [ff]
      exact directory
    rw [← ff]
    exact CompactBatch.mem_prepared_iff_of (by decide : entry.deterministic = true)
      (by decide : entry.withoutAccept = true) prep (CompactMachine.mem_choices gen n routines)
      (by omega) endRoom (es := es) (bits := bits)
  · have hw : 0 < w := by cases w with
      | zero => simp at frame
      | succ w => exact Nat.zero_lt_succ w
    rw [CompactBatch.sum_prepared_of (by decide : entry.unsigned = true) prep]
    rw [CompactPacket.sum_typed_directory pub translate cells hw (fun i hi own => (args i hi own).1)
      (fun i hi own => (args i hi own).2.1) (fun i hi own => (args i hi own).2.2)
      (fun i hi own => depth i hi ((owner i hi) ▸ own)) (fun i hi own => compiler i hi ((owner i hi) ▸ own))]
    have same : f.ownedRows mt 0 f.count = f.ownedRows m 0 f.count := by
      apply List.filter_congr
      intro i hi
      rw [owner i (by simpa using hi)]
    rw [same]

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
