import OAI.Computability.VPVNP.PairShrinkCallWorkspace
import OAI.Computability.VPVNP.PairShrinkCallDemandCells
import OAI.Computability.VPVNP.PairShrinkCallSupplyCells
import OAI.Computability.VPVNP.PairSimulationRecordedMapCalls

/-!
# A native map-call descriptor from a selected shrinking term

The real demand and supply readbacks, the recorded branch widths and the
private workspace intervals supply every input of the compiled descriptor
writer. These facts hold for arbitrary choices of the local half-wires and
absorbed words, including data on which the grouped entry test rejects.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPreparedCall

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion MotifEntry NetworkKernel
open MapPortAgreement MapResidentAgreement
open scoped Fin.CommRing

variable {a g b pad w p r k t n limit endAddr : ℕ} {K : Type} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (X : State a (packingLaneBits a g))
/-- Classical decidable equality on the compression state’s base vertices for the native
map-call descriptor of a selected shrink term. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _
variable (selection : X.ShrinkSelection F) (layout : Bool) (subdiv : Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad) (hpos : ∀ t, 0 < subdiv t)
variable (m : X.packingData.Motif) (j : Fin 6)
/-- Demand widths of a motif computed from the numbering and wire widths of the input state. -/
noncomputable abbrev widthsDemand (motif : X.packingData.Motif) :=
  X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth motif

local notation "BW" => widthsDemand X m
/-- Supply widths of a motif for the term chosen by the shrinking selection. -/
noncomputable abbrev width (e : X.packingData.Motif) :=
  X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth F e (selection e)

local notation "Widths" => width F X selection
local notation "Idx" => Fin.val (CompressorRecords.ShrinkMotifOrder.stateNumber X m)
local notation "U" => repetitions F (BW)

variable (old : ShrinkCallDemandCells.Old X layout m j)
variable (hidden : Placed (X.packingData.shrinkInternalOwner layout)
  (internalLabel (width F X selection) layout)
  (X.packingData.shrinkPartySite layout m j))
variable (z : (X.shrinkOutputState layout subdiv
  (fun m t ↦ width F X selection m (layout, t)) I).network.Half
  (X.packingData.shrinkPartySite layout m j))

/-- The full selected input, with the original matrix coordinates at this party. -/
noncomputable def input : LocalHistory.EntryInput F :=
  ⟨BW, (selection m).val, j, X.packingData.shrinkLocalDemandArg (State.two_le_packingColors a)
    (Nat.two_pow_pos a) X.shrinkNumber X.shrinkOrder X.packingWidth layout m j old,
    X.packingData.shrinkLocalSupplyArg layout subdiv (Widths) I hpos m j hidden z⟩

local notation "C" => input F X selection layout subdiv I hpos m j old hidden z
local notation "D" => demandBits demandSource demandTarget j
  (LocalHistory.EntryInput.demandBits (C))
local notation "S" => MotifSelector.mapHalf supply (fun _ ↦ inputBits)
  (LocalHistory.EntryInput.supplyBits (C))

variable (s : ShrinkCallFields.Scratch) (arena : NodeArguments.Arena) (nodes : X.network.Site → ℕ)
local notation "cd" => ShrinkCallDemandCells.cdBase X m arena nodes

variable (A : MapEntryTable.Allocation F (demandGrid F demandMass_pos (widthsDemand X m)) j r k)
variable (loc : A.Address → Fin p)
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit)
  (u := repetitions F (widthsDemand X m)) (t := t) F (widthsDemand X m) (selection m).val
  s (CompressorRecords.ShrinkMotifOrder.stateNumber X m).val
    (ShrinkCallDemandCells.cdBase X m arena nodes))
local notation "HW" => ShrinkCallFields.workspace F (A.program loc)
  (BW) (Subtype.val (selection m))
  (D) (S)
  s Idx layout (cd) ok

private theorem endpoint_le (q : Bool × Bool) : (MapRow.endpoint demandSource demandTarget j
    (BW) (D) q).1 ≤ BW q.2 := by
  rcases q with ⟨dir, e⟩
  cases dir with
  | false =>
    by_cases eqn : j = demandSource e <;>
      simp [MapRow.endpoint, eqn]
  | true =>
    by_cases eqn : j = demandTarget e <;>
      simp [MapRow.endpoint, eqn]

/-- The descriptor's scalar and address words agree with the map initializer's
precise ABI, including its separate directory, ordinal and label addresses. -/
theorem values_eq (arg : ShrinkCallFields.Arg) :
    ShrinkCallFields.values (w := w) X F selection m s j layout (cd) arg =
      MapCallSetup.values A loc (HW) arg := by
  cases arg with
  | base f => rfl
  | demand e => rfl
  | payload e => rfl
  | copies => rfl
  | hist => rfl
  | directory => rfl
  | source => exact congrArg (fun n : ℕ ↦ (n : Word w)) (ShrinkCallFields.workspace_source ..).symm
  | target => exact congrArg (fun n : ℕ ↦ (n : Word w)) (ShrinkCallFields.workspace_target ..).symm

/-- Every incident bit is the local matrix's actual coordinate. Descriptor
writes and the directory fill are disjoint from all these reads. -/
theorem resident (before after : Word w → Word w)
    (demand : ShrinkCallDemandCells.Readback X layout m j arena nodes old after s.staging endAddr)
    (shared : ShrinkCallSupplyCells.Absorbed X layout (Widths) m j s hidden after)
    (visible : ShrinkCallSupplyCells.Retained X layout subdiv (Widths) I m j s z before after) :
    MapArgumentWriter.ResidentFields A loc (HW) (s.descriptor : Word w) after := by
  let bases := s.fieldBase Idx j layout (cd)
  have endStaging : s.directory < 2 ^ w := by
    have room := ok.room.trans_lt ok.capacity.room
    unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source
      ShrinkCallFields.Scratch.descriptor at room
    omega
  have survFit (dir : Bool) (e : Fin 4) : s.surviving dir e + (Widths) m (layout, e) ≤ 2 ^ w :=
    (Nat.add_le_add_left (ok.supply _) _).trans ((s.surviving_end dir e).trans endStaging.le)
  constructor
  · intro e
    have small := ok.supply e
    have all := s.surviving_end false 0
    omega
  · intro q
    rfl
  · intro q i
    cases q with
    | inl q =>
      obtain ⟨e, party⟩ := q
      have bit := ShrinkCallSupplyCells.read X layout subdiv (Widths) I hpos m j s hidden z
        before after shared visible survFit (cd) false e party i
      have sep := ShrinkCallFields.separated (BW) (selection m).val (D) (S) s Idx layout
        (cd) ok A loc (.inr (false, e)) i
      change after ((bases (.inr (false, e)) : Word w) + (i.val : Word w)) = _ ∧ _
      constructor
      · rw [← Nat.cast_add]
        exact bit
      · change MapArgumentWriter.separated A loc (HW) _
          ((bases (.inr (false, e)) : Word w) + (i.val : Word w))
        rw [← Nat.cast_add]
        exact sep
    | inr q =>
      obtain ⟨e, party⟩ := q
      have bit := ShrinkCallSupplyCells.read X layout subdiv (Widths) I hpos m j s hidden z
        before after shared visible survFit (cd) true e party i
      have sep := ShrinkCallFields.separated (BW) (selection m).val (D) (S) s Idx layout
        (cd) ok A loc (.inr (true, e)) i
      change after ((bases (.inr (true, e)) : Word w) + (i.val : Word w)) = _ ∧ _
      constructor
      · rw [← Nat.cast_add]
        exact bit
      · change MapArgumentWriter.separated A loc (HW) _
          ((bases (.inr (true, e)) : Word w) + (i.val : Word w))
        rw [← Nat.cast_add]
        exact sep
  · intro q i
    have bit := ShrinkCallDemandCells.scratch_demandCells X layout m j arena nodes s Idx old
      after endAddr demand q i
    exact ⟨bit, ShrinkCallFields.separated (BW) (selection m).val (D) (S) s Idx layout
      (cd) ok A loc (.inl q) ⟨i.val, i.isLt.trans_le
        (endpoint_le F X selection layout subdiv I hpos m j old hidden z q)⟩⟩

end PairSimulation.ShrinkPreparedCall

end VPVNP
end Computability
end OAI
