import OAI.Computability.VPVNP.PairShrinkJobPrepared
import OAI.Computability.VPVNP.PairSimulationMapHandlerFrame

/-!
# The ready continuation of the scheduled shrink row

The interval copier leaves the five shared operand registers and the state
register intact. The native grouped map can therefore start from every
actual exit of the gather, including calls with invalid selector payloads.
The descriptor and all mutable map ranges lie above the pending DFS stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.State Compression.PackingData
open Compression.ShrinkMotif Compression.ShrinkEnergy NetworkKernel MotifBlocks MotifGrid
open MotifConversion CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.ShrinkSlots
open scoped Fin.CommRing

variable {a b g w p r t n limit endAddr : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (degree : ℕ) (ord : B.Entry → Fin t)
variable {δ : ℝ} (X : State a (packingLaneBits a g))
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (sel : X.ShrinkSelection B.shrink)
variable (m : X.packingData.Motif) (j : Fin 6) (J : Job X B.shrink ready sel m j w)
private noncomputable local instance readyBase : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "BW" => ShrinkPreparedCall.widthsDemand X m
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel))
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m j))
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (ShrinkPreparedCall.widthsDemand X m)) B.shrink
  (ShrinkPreparedCall.widthsDemand X m) (sel m).val J.scratch (ShrinkMotifOrder.stateNumber X m).val
  (ShrinkCallDemandCells.cdBase X m J.arena J.nodes))
local notation "call" => Job.entryInput B X ready sel m j J hidden
local notation "family" => ShrinkCallABI.family B degree a ord
local notation "work" => Job.mapWorkspace B degree ord X ready sel m j J hidden ok
local notation "O" => ShrinkCallABI.operands degree

variable (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin 24 ↪ Fin r)
variable (mem : Memory w) (pub : Fin 5 → Word w) (st level : Word w)
variable (T : IncidenceDirectory w) (origin : ℕ)
variable (tables : J.OldPublished (ShrinkCallABI.operands degree) pub st mem level T origin)

include tables in
/-- The callback required by the scheduled resident loop, with all six operands
taken from the actual post-gather registers. -/
theorem Job.ready_after_gather (c : Config w p r)
    (children : J.ChildWords c.privateMem endAddr)
    (ends : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.staging)
    (guessed : ShrinkCallSupplyCells.Absorbed X (side) (widths) m j J.scratch hidden c.privateMem)
    (two : 2 < 2 ^ w) (termRoom : ShrinkInput.termEnd X origin 10 < 2 ^ w)
    (pairs : ShrinkTermInputs.statePairs X (ShrinkInput.demandHead X origin) mem)
    (terms : TermRecordScan.Fields B.shrink ShrinkSliceArrays.supplyRoles demandMass_pos
      (BW) (sel m).val (ShrinkTermSelection.rowBase X (ShrinkInput.termHead X origin) 10 m) mem) :
    ∀ out : Config w p r, J.Assembled c.privateMem out.privateMem →
      MapHandlerOperand.pub (family) demandMass_pos (call) dfs saved common out = pub →
      MapHandlerOperand.state (family) demandMass_pos (call) dfs saved common out = st →
      MapHandlerOperand.Prepared (family) demandMass_pos (call) dfs saved common out mem
        (work) := by
  intro out result hpub hst
  change ShrinkCallABI.pub out common = pub at hpub
  change ShrinkCallABI.state out common = st at hst
  apply Job.prepared_after_gather B degree ord X ready sel m j J hidden ok dfs saved common out mem
    c.privateMem result children ends guessed T origin level _ two termRoom pairs terms
  rwa [hpub, hst]

include tables in
private theorem descriptor_read :
    ((O).inputs a).descriptor.eval pub st mem = (J.scratch.descriptor : Word w) := by
  have vertex : ((O).cell 0).eval pub st mem = (Fintype.card X.Base : Word w) := by
    change mem ((O).level.eval pub st mem + 0).val = _
    rw [tables.live.header]
    exact tables.levelData.vertices
  have lane : ((O).cell 3).eval pub st mem = ((2 ^ g : ℕ) : Word w) := by
    change mem ((O).level.eval pub st mem + 3).val = _
    rw [tables.live.header]
    exact tables.levelData.residual
  have count := ShrinkCallHeader.count_eq X (O) pub st mem vertex lane
  change (((O).hidden.eval pub st mem +
    (4 * ((O).count a).eval pub st mem) * (O).slotStride.eval pub st mem) +
      9 * (O).slotStride.eval pub st mem) + 16 = _
  rw [count, ← tables.motifCount, tables.live.hiddenBase, tables.live.stride]
  simp only [ShrinkCallFields.Scratch.descriptor, ShrinkCallFields.Scratch.directory,
    ShrinkCallFields.Scratch.staging, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

include tables in
/-- The descriptor writer and the four mutable map arrays preserve the DFS
stack, including for unsuccessful resident entries. -/
theorem Job.call_bounds (stack : endAddr ≤ J.scratch.hist) :
    MapHandlerOperand.Bounds (family) demandMass_pos (call) (work) endAddr
      (((family).base (MapHandlerOperand.index demandMass_pos (call))).eval pub st mem) := by
  have dptr := descriptor_read B degree X ready sel m j J mem pub st level T origin tables
  change ((O).inputs a).descriptor.eval pub st mem = _ at dptr
  have extent := ok.room.trans_lt ok.capacity.room
  unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source
    ShrinkCallFields.Scratch.descriptor at extent
  have cap : J.scratch.directory + 16 < 2 ^ w := by omega
  have dcap : (J.scratch.directory : Word w).val = J.scratch.directory :=
    Nat.mod_eq_of_lt (by omega)
  have bound := ok.histogram
  constructor
  · change endAddr ≤ (((O).inputs a).descriptor.eval pub st mem).val
    rw [dptr]
    change endAddr ≤ (J.scratch.directory + 16) % (2 ^ w)
    rw [Nat.mod_eq_of_lt cap]
    omega
  · change endAddr ≤ MapWorkspace.ordinalBase Bool (Bool × Fin 4) J.scratch.directory
    unfold MapWorkspace.ordinalBase MapWorkspace.descriptorBase
    omega
  · change endAddr ≤ MapWorkspace.ordinalBase Bool (Bool × Fin 4) J.scratch.directory + _
    unfold MapWorkspace.ordinalBase MapWorkspace.descriptorBase
    omega
  · exact stack
  · change endAddr ≤ (J.scratch.directory : Word w).val
    rw [dcap]
    omega
  · change (J.scratch.directory : Word w).val + _ ≤ _
    rw [dcap]
    have len := MapPortAgreement.ports_length_le supply j
      (MapHandlerOperand.layout (family) demandMass_pos (call)).core.edgeOrder
    have card : 2 * Fintype.card (Bool × Fin 4) = 16 := by simp
    rw [card] at len
    exact (Nat.add_le_add_left len _).trans cap.le

/-- Counter words lie below the upper private region overwritten by interval copies. -/
theorem Job.histogram_before_staging (hist : J.scratch.hist + t ≤ J.scratch.hidden) (l : Fin t) :
    (((work).hist + l.val : ℕ) : Word w).val < J.scratch.staging :=
  (Nat.mod_le ..).trans_lt (((Nat.add_lt_add_left l.isLt _).trans_le hist).trans_le
    (Nat.le_add_right ..))

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
