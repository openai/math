import OAI.Computability.VPVNP.PairShrinkResidentMemory
import OAI.Computability.VPVNP.PairSimulationShrinkLiveOperands
import OAI.Computability.VPVNP.PairShrinkVertexImage

/-!
# Live resident operands for one physical shrinking map

The resident loop carries the old header, term pointer, constant stride,
one word and the writer's five public inputs in the same eight shared
registers throughout. Packet and shared-field readbacks are those of the
loop-entry private memory. The fixed map row runs against its own selected
motif, while its exterior frame maintains these inputs for the next row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkVertexImage

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords
open ShrinkMapImage ShrinkMapImage.Registers ShrinkResidentMemory
open scoped Fin.CommRing

/-- Live registers at a map-row entrance. Header registers 0, 4, 5 and
10 and the five public operands share the old-level register 11. -/
def residentSlot : Fin 8 → Fin 24 := ![11, 16, 17, 22, 0, 9, 10, 8]

/-- A host register is live at a resident map entrance when it is the image of one of the eight
operand slots. -/
def residentLive {r : ℕ} (common : Fin 24 ↪ Fin r) (q : Fin r) :=
  ∃ j : Fin 8, common (residentSlot j) = q

theorem live_protected {r : ℕ} (common : Fin 24 ↪ Fin r) (tmp : Fin r)
    (apart : ∀ j, common j ≠ tmp) (j : Fin 8) :
    Protected mapRegisters common tmp (common (residentSlot j)) := by
  have disjoint : ∀ i : Fin 8, residentSlot i ≠ mapRegisters.zero ∧
      ∀ k : Fin 11, 6 ≤ k.val → k.val ≤ 9 → residentSlot i ≠ mapRegisters.header k := by decide
  exact ⟨apart _, common.injective.ne (disjoint j).1,
    fun k lo hi ↦ common.injective.ne ((disjoint j).2 k lo hi)⟩

/-- The resident loop's cursor can advance without changing any live map
operand register. -/
theorem residentLive_cursor {r : ℕ} (common : Fin 24 ↪ Fin r) (q : Fin r)
    (live : residentLive common q) : q ≠ (mapRegisters.headerReg common) 2 := by
  obtain ⟨j, rfl⟩ := live
  apply common.injective.ne
  exact (by decide : ∀ i : Fin 8, residentSlot i ≠ mapRegisters.header 2) j

end PairSimulation.ShrinkVertexImage

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion MotifEntry NetworkKernel CompressorRecords
open CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open ShrinkVertexImage ShrinkMapImage.Registers ShrinkResidentMemory

variable {w p r t n limit endAddr g : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (ord : B.Entry → Fin t) (stage : Fin S.steps)
variable {X : State (a stage) (packingLaneBits (a stage) g)}
variable (sel : X.ShrinkSelection B.shrink) {motif : X.packingData.Motif} {party : Fin 6}
variable (J : Job X B.shrink (S.shrink stage) sel motif party w)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Fam" => matrixFamily B ord stage
local notation "degree" => slotDegree S
local notation "BW" => ShrinkPreparedCall.widthsDemand X motif
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X motif)
local notation "cd" => ShrinkCallDemandCells.cdBase X motif J.arena J.nodes

variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel))
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) motif party))
local notation "call" => Job.entryInput B X (S.shrink stage) sel motif party J hidden

variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (ShrinkPreparedCall.widthsDemand X motif)) B.shrink
  (ShrinkPreparedCall.widthsDemand X motif) (sel motif).val J.scratch
  (ShrinkMotifOrder.stateNumber X motif).val (ShrinkCallDemandCells.cdBase X motif J.arena J.nodes))

variable (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin 24 ↪ Fin r)
variable (tmp : Fin r) (entry : Config w p r) (st : Word w) (mem : Memory w) (level term : Word w)
local notation "P" => ShrinkCallABI.pub entry common
local notation "work" =>
  Job.mapWorkspace B degree ord X (S.shrink stage) sel motif party J hidden ok
local notation "guard" => residentLive common
local notation "inv" => fun (_ : Word w) (c : Config w p r) ↦
  Invariant J.scratch entry.privateMem guard entry.reg c

set_option maxHeartbeats 1300000 in
-- The grouped entry and the selected stage's gather share dependent map registers and field widths.
/-- Supply the non-static inputs of the exact row interpreter from the
loop-entry configuration and the chronological source readbacks. -/
theorem Job.liveOperands {T : IncidenceDirectory w} {origin : ℕ}
    (apart : ∀ j, common j ≠ tmp) (head : entry.reg (common 11) = level)
    (termAt : entry.reg (common 16) = term) (strideAt : entry.reg (common 17) = 10)
    (oneAt : entry.reg (common 22) = 1)
    (packets : J.Packets endAddr entry.privateMem)
    (children : J.ChildWords entry.privateMem endAddr)
    (hiddenAt : ShrinkCallSupplyCells.Absorbed X side widths motif party J.scratch hidden
      entry.privateMem)
    (childrenLow : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.hist)
    (parentLow : J.arena.base J.node + J.arena.stride ≤ J.scratch.hist)
    (histEnd : J.scratch.hist + t ≤ J.scratch.hidden)
    (old : J.OldPublished (ShrinkCallABI.operands degree) P st mem level T origin)
    (two : 2 < 2 ^ w) (termRoom : ShrinkInput.termEnd X origin 10 < 2 ^ w)
    (pairs : ShrinkTermInputs.statePairs X (ShrinkInput.demandHead X origin) mem)
    (terms : TermRecordScan.Fields B.shrink ShrinkSliceArrays.supplyRoles demandMass_pos
      BW (sel motif).val (ShrinkTermSelection.rowBase X (ShrinkInput.termHead X origin) 10 motif)
      mem)
    (node : Word w) (c : Config w p r) (valid : inv node c) :
    LiveOperands (endAddr := endAddr) Fam mapRegisters dfs saved common tmp call J P st mem
      level term work inv node c := by
  have reg (l : Fin 8) := valid.registers (common (residentSlot l)) ⟨l, rfl⟩
  have hiddenFit (t : Fin 4) : widths motif (!side, t) ≤ J.scratch.stride := ok.supply (!side, t)
  have stageRoom : J.scratch.staging ≤ 2 ^ w := by
    have room := ok.room.trans_lt ok.capacity.room
    unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source
      ShrinkCallFields.Scratch.descriptor ShrinkCallFields.Scratch.directory at room
    omega
  have histStage : J.scratch.hist ≤ J.scratch.staging :=
    (Nat.le_add_right ..).trans (histEnd.trans (Nat.le_add_right ..))
  refine ⟨(reg 0).trans head, (reg 1).trans termAt, (reg 2).trans strideAt, (reg 3).trans oneAt,
    ?_, J.packets_preserved valid.memory packets childrenLow parentLow, ?_, ?_⟩
  · intro j
    have publicSlots : ∀ j : Fin 5, ∃ l : Fin 8,
        residentSlot l = ShrinkCallABI.sourceSlot j.castSucc := by decide
    obtain ⟨l, hl⟩ := publicSlots j
    change c.reg (common (ShrinkCallABI.sourceSlot j.castSucc)) =
      entry.reg (common (ShrinkCallABI.sourceSlot j.castSucc))
    rw [← hl]
    exact reg l
  · intro out staged pubEq stateEq
    have table : J.OldPublished (ShrinkCallABI.operands degree) (ShrinkCallABI.pub out common)
        (ShrinkCallABI.state out common) mem level T origin := by
      change ShrinkCallABI.pub out common = P at pubEq
      change ShrinkCallABI.state out common = st at stateEq
      rw [pubEq, stateEq]
      exact old
    exact Job.prepared_after_gather B degree ord X (S.shrink stage) sel motif party J hidden ok dfs
      saved common out mem c.privateMem staged
      (J.childWords_preserved valid.memory children childrenLow)
      (fun u ↦ (childrenLow u).trans histStage)
      (J.absorbed_preserved hidden valid.memory hiddenAt ok.ordinal hiddenFit stageRoom)
      T origin level table two termRoom pairs terms
  · intro out kept frame
    apply Job.keepsInputs B degree ord X (S.shrink stage) sel motif party J hidden ok valid
      _ histEnd P st mem old frame
    intro q ⟨l, hq⟩
    rw [← hq]
    exact kept _ (live_protected common tmp apart l)

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
