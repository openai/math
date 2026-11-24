import OAI.Computability.VPVNP.PairShrinkPreparedCall
import OAI.Computability.VPVNP.PairShrinkCallFamily
import OAI.Computability.VPVNP.PairSimulationMapHandlerOperand

/-!
# Preparing the selected shrink handler's fixed map image

The stage and the party determine the descriptor recipe. The live register
bank and the completed argument gathers supply its true addresses and bits.
Its histogram is disjoint from both the private descriptor and the local
port directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPreparedCall

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open CompressorRecords MotifGrid MotifBlocks MotifConversion MotifEntry NetworkKernel
open scoped Fin.CommRing

variable {a g b pad w p r t n limit endAddr : ℕ} {K : Type} [_root_.Field K]
variable {S : BlockSchedule K} (B : S.Templates)
variable (degree : ℕ) (ord : B.Entry → Fin t)
variable (X : State a (packingLaneBits a g))
/-- Classical decidable equality on the compression state’s base vertices for preparing the
shrink handler’s map descriptor. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _
variable (selection : X.ShrinkSelection B.shrink) (layout : Bool) (subdiv : Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad) (hpos : ∀ t, 0 < subdiv t)
variable (m : X.packingData.Motif) (j : Fin 6)
variable (old : ShrinkCallDemandCells.Old X layout m j)
variable (hidden : Placed (X.packingData.shrinkInternalOwner layout)
  (internalLabel (width B.shrink X selection) layout) (X.packingData.shrinkPartySite layout m j))
variable (z : (X.shrinkOutputState layout subdiv
  (fun m t ↦ width B.shrink X selection m (layout, t)) I).network.Half
    (X.packingData.shrinkPartySite layout m j))
variable (s : ShrinkCallFields.Scratch) (arena : NodeArguments.Arena) (nodes : X.network.Site → ℕ)
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (widthsDemand X m)) B.shrink (widthsDemand X m) (selection m).val
  s (ShrinkMotifOrder.stateNumber X m).val (ShrinkCallDemandCells.cdBase X m arena nodes))

local notation "Call" => input B.shrink X selection layout subdiv I hpos m j old hidden z
local notation "Family" => ShrinkCallABI.family B degree a ord
local notation "Grid" => MapHandlerOperand.index demandMass_pos (Call)
local notation "L" => MapHandlerOperand.layout (Family) demandMass_pos (Call)
local notation "Prog" => MapInline.callProgram (L)
local notation "Ds" => demandBits demandSource demandTarget j
  (LocalHistory.EntryInput.demandBits (Call))
local notation "Ws" => MotifSelector.mapHalf supply (fun _ ↦ inputBits)
  (LocalHistory.EntryInput.supplyBits (Call))
local notation "cds" => ShrinkCallDemandCells.cdBase X m arena nodes
local notation "Workspace" => ShrinkCallFields.workspace B.shrink (Prog) (widthsDemand X m)
  (Subtype.val (selection m)) (Ds) (Ws) s
  (Fin.val (ShrinkMotifOrder.stateNumber X m)) layout (cds) ok

variable (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin 24 ↪ Fin r)
variable (cfg : Config w p r) (mem : Memory w)
local notation "pub" => MapHandlerOperand.pub (Family) demandMass_pos (Call) dfs saved common cfg
local notation "st" => MapHandlerOperand.state (Family) demandMass_pos (Call) dfs saved common cfg
local notation "O" => ShrinkCallABI.operands degree
local notation "Addr" => MapHandlerOperand.addr (Family) demandMass_pos (Call)
  dfs saved common cfg mem

set_option maxHeartbeats 1200000 in
-- The handler, typed old packet and selected map layout use dependent coordinate types.
/-- The hosted handler can run the selected entry, on the actual private words
and the descriptor expressions compiled for the current stage. -/
theorem prepared (before : Word w → Word w)
    (oldFields : ShrinkCallDemandCells.Readback X layout m j arena nodes old cfg.privateMem
      s.staging endAddr)
    (hiddenFields : ShrinkCallSupplyCells.Absorbed X layout (width B.shrink X selection) m j
      s hidden cfg.privateMem)
    (supplyFields : ShrinkCallSupplyCells.Retained X layout subdiv (width B.shrink X selection)
      I m j s z before cfg.privateMem)
    (words : ∀ arg, (((O).inputs a).fields j arg).eval pub st mem =
      ShrinkCallFields.values (w := w) X B.shrink selection m s j layout (cds) arg) :
    MapHandlerOperand.Prepared (Family) demandMass_pos (Call) dfs saved common cfg mem
      (Workspace) := by
  have hdir := words .directory
  change ((O).inputs a).directory.eval pub st mem = (s.directory : Word w) at hdir
  have address : Addr = (s.descriptor : Word w) := by
    change ((O).inputs a).directory.eval pub st mem + 16 = _
    rw [hdir]
    simp [ShrinkCallFields.Scratch.descriptor]
  have limit := ok.room.trans_lt ok.capacity.room
  have hroom := ShrinkCallFields.workspace_descriptor_fit B.shrink (widthsDemand X m)
    (selection m).val s _ (cds) ok
  have hdesc : (s.descriptor : Word w).val = s.descriptor := Nat.mod_eq_of_lt (by
    unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source at limit
    omega)
  have hhist (l : Fin t) : s.hist + l.val < s.directory :=
    (Nat.add_lt_add_left l.isLt s.hist).trans_le ok.histogram
  have endDir : s.directory + 16 < 2 ^ w := by
    unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source
      ShrinkCallFields.Scratch.descriptor at limit
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rwa [address, hdesc]
  · intro arg
    exact (words arg).trans (values_eq B.shrink X selection layout subdiv I hpos m j old hidden z
      s arena nodes (L).core ((L).corePC (L).locations) ok arg)
  · rw [address]
    exact resident B.shrink X selection layout subdiv I hpos m j old hidden z s arena nodes
      (L).core ((L).corePC (L).locations) ok before cfg.privateMem oldFields hiddenFields
      supplyFields
  · intro l
    left
    change ((s.hist + l.val : ℕ) : Word w).val < (Addr).val
    rw [address, hdesc, show ((s.hist + l.val : ℕ) : Word w).val = _ from
      Nat.mod_eq_of_lt (by have := hhist l; omega)]
    exact (hhist l).trans_le (Nat.le_add_right ..)
  · intro l i eqn
    have hi := i.isLt.trans_le (MapPortAgreement.ports_length_le supply j (L).core.edgeOrder)
    change i.val < 2 * Fintype.card (Bool × Fin 4) at hi
    have card : 2 * Fintype.card (Bool × Fin 4) = 16 := by simp
    rw [card] at hi
    have hv := congrArg Fin.val eqn
    change ((s.hist + l.val : ℕ) : Word w).val =
      ((s.directory : Word w) + (i.val : Word w)).val at hv
    rw [← Nat.cast_add, Fin.val_natCast, Fin.val_natCast,
      Nat.mod_eq_of_lt (by have := hhist l; omega : s.hist + l.val < 2 ^ w),
      Nat.mod_eq_of_lt (by omega : s.directory + i.val < 2 ^ w)] at hv
    have := hhist l
    omega

end PairSimulation.ShrinkPreparedCall

end VPVNP
end Computability
end OAI
