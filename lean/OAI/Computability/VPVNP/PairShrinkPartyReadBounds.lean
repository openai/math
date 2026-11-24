import OAI.Computability.VPVNP.PairShrinkPartyABReads
import OAI.Computability.VPVNP.PairShrinkSurvivingReadBounds
import OAI.Computability.VPVNP.PairSimulationFieldReadSafety

/-!
# External read region of the selected shrinking-party gather

All runtime reads of the emitted gather come from the two level headers,
the old sorted-bundle tables, the output incidence and width columns, the
absolute motif and inverse-slot tables, or the assigned slice banks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open Compression.ShrinkEnergy MotifBlocks MotifGrid MotifConversion CompressorRecords
open CompressorRecords.ShrinkSlots CompressorRecords.ShrinkSliceSweep
open CompressorRecords.PhaseRecipe ShrinkPartyColumns
open scoped Fin.CommRing

variable {a b g w : ℕ} {δ factor : ℝ} {K : Type*} [_root_.Field K]
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : ShrinkMotif.Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6} (J : Job X F ready sel m party w)
local notation "shape" => levelShape (b := b) X
local notation "sub" => SlotLevel.Shape.subdivisions (levelShape (b := b) X)
local notation "side" => selectedLayout X F sel
local notation "idx" => ShrinkMotifOrder.stateNumber X m
local notation "count" => 2 ^ (Shrink.colors a) * 2 ^ a / 4
local notation "N" => Fintype.card (State.Base (X.shrinkNext F ready sel)) * 2 ^ g * 2 ^ b

/-- The selected next-state arrays and the interval bank lie below the terminal header.
The pointer in old header cell 40 is the same next header used to look up the incidence heads. -/
structure Job.SupplyAreas (level absolute : Word w) (heads : SlotLevel.Heads)
    (U : IncidenceDirectory w) (nextHead H : ℕ) (mem : Memory w) : Prop where
  pointer : mem (level.val + 40) = (nextHead : Word w)
  header : nextHead + 60 ≤ H
  motifs : absolute.val + ShrinkTermInputs.motifCount X ≤ H
  inverse : SlotLevel.targetsHead shape heads ≤ H
  incoming : U.actualIn.val + N ≤ H
  widths : U.width.val + N ≤ H
  intervals : J.allocation.last ≤ H

variable {pub : Fin 5 → Word w} {state level absolute : Word w} {mem : Memory w}
variable {origin nextHead layer pitch : ℕ} {T U : IncidenceDirectory w} {heads : SlotLevel.Heads}

theorem Job.readSafe (O : ShrinkCallHeader.Operands) (node : Expr) (H : Word w)
    (terminalRoom : H.val + 31 < 2 ^ w)
    (old : J.OldPublished O pub state mem level T origin)
    (next : J.SupplyPublished O node pub state mem heads absolute U layer pitch)
    (ins : InputsReadable O H.val pub state mem)
    (nodeSafe : node.ReadsFrom (· < H.val) pub state mem)
    (oldSpace : J.ABAreas level T origin H.val)
    (space : J.SupplyAreas level absolute heads U nextHead H.val mem)
    (c : At party side) (i : Fin (frames count sub c.val)) :
    (J.row c i).ReadSafe (setups O node a b party side c i) (TerminalLink.workerCell H)
      pub state mem := by
  have below : (J.row c i).ReadSafe (setups O node a b party side c i) (· < H.val)
      pub state mem := by
    rcases c with ⟨_ | ⟨dir, t⟩, hc⟩
    · obtain ⟨loads, cells⟩ := J.ab_readBounds O node old ins oldSpace hc i
      exact ⟨loads, cells⟩
    · let P := supplyInputs O node a dir t
      have oldRoom : (O.level.eval pub state mem).val + 42 < H.val := by
        rw [old.live.header]; have := oldSpace.levelEnd; omega
      have nextRoom : ((ShrinkSurvivingSelected.cell O.level 40).eval pub state mem).val + 59 <
          H.val := by
        change (mem (O.level.eval pub state mem + (40 : Word w)).val).val + 59 < _
        rw [old.live.header, Fin.val_add]
        have len : (40 : Word w).val = 40 := by
          change 40 % (2 ^ w) = 40
          exact Nat.mod_eq_of_lt (by omega)
        have nextFit : nextHead < 2 ^ w := by have := space.header; omega
        rw [len, Nat.mod_eq_of_lt (by have := oldSpace.levelEnd; omega),
          space.pointer, Fin.val_natCast, Nat.mod_eq_of_lt nextFit]
        have := space.header
        omega
      obtain ⟨table, fields⟩ := ShrinkSurvivingReadBounds.inputs_reads a O.level O.motif O.arguments
        O.argumentStride node ((O.inputs a).surviving dir t) ins.level ins.motif ins.arguments
        ins.stride oldRoom nextRoom
      have dst := ShrinkSurvivingReadBounds.destination_reads O a dir t ins.level ins.hidden
        ins.slot (by omega)
      have denseLt : (idx).val < ShrinkTermInputs.motifCount X :=
        ((ShrinkMotifOrder.entries X).symm m).isLt
      have absRoom := (Nat.add_lt_add_left denseLt absolute.val).trans_le space.motifs
      refine ⟨ShrinkSurvivingReadBounds.setup_reads X P m t dir i ready side (branchWidth X F sel)
        heads absolute (next.tableHeads dir t) table next.directory next.sorted next.absFit
        absRoom space.inverse next.slotFit next.degreeFit next.twoFit U J.arena
        (next.half dir t) fields nodeSafe dst next.incidence next.capacity space.incoming
        space.widths, ?_⟩
      intro k
      have frame := (ShrinkSurvivingReadBounds.frame_end J.allocation next.allocation idx t i)
        |>.trans_le space.intervals
      change ShrinkSurvivingFrames.head (J.allocation.row (idx, t)) (sub t) i + k.val < _
      exact (Nat.add_le_add_left (show k.val ≤ 2 from Nat.le_of_lt_succ k.isLt) _).trans_lt frame
  exact ⟨fun j ↦ TerminalLink.expr_worker_reads terminalRoom (below.loads j),
    fun k ↦ TerminalLink.workerCell_of_lt terminalRoom (below.frame k)⟩

/-- The six concrete register operands satisfy the whole-program read condition using
only the assigned table extents and the published level pointers. -/
theorem Job.abi_readSafe (degree : ℕ) (H : Word w) (terminalRoom : H.val + 31 < 2 ^ w)
    (old : J.OldPublished (ShrinkCallABI.operands degree) pub state mem level T origin)
    (next : J.SupplyPublished (ShrinkCallABI.operands degree) ShrinkCallABI.node pub state mem heads
      absolute U layer pitch)
    (oldSpace : J.ABAreas level T origin H.val)
    (space : J.SupplyAreas level absolute heads U nextHead H.val mem)
    (c : At party side) (i : Fin (frames count sub c.val)) :
    (J.row c i).ReadSafe
      (setups (ShrinkCallABI.operands degree) ShrinkCallABI.node a b party side c i)
      (TerminalLink.workerCell H) pub state mem :=
  J.readSafe _ _ H terminalRoom old next (J.abi_inputs_readable degree old oldSpace) trivial
    oldSpace space c i

variable (degree : ℕ) (H : Word w)
local notation "operands" => ShrinkCallABI.operands degree
local notation "flatSetup" =>
  gather party side count sub (setups operands ShrinkCallABI.node a b party side)
local notation "flatRow" => gather party side count sub (Job.row J)

/-- The concrete ABI run excludes the terminal control cells. Both the returning upper
scratch and the successful trace are explicit functions of the decoded resident inputs. -/
theorem native_party_worker {p r k : ℕ}
    (terminalRoom : H.val + 31 < 2 ^ w)
    (old : J.OldPublished operands pub state mem level T origin)
    (next : J.SupplyPublished operands ShrinkCallABI.node pub state mem heads absolute U
      layer pitch)
    (oldSpace : J.ABAreas level T origin H.val)
    (space : J.SupplyAreas level absolute heads U nextHead H.val mem)
    (M : Machine w p r k) (vm : ∀ i, Fin (RegisterSetup.regCount ((flatSetup i).operands)) ↪ Fin r)
    (inputs : Fin 6 → Fin r) (loc : ResidentColumn.Label flatSetup → Fin p) (ret : Fin p)
    (code : ∀ l, M.code (loc l) = ResidentColumn.instruction flatSetup vm inputs loc ret l)
    (safe : ∀ i v j, vm i v ≠ inputs j)
    (cfg : Config w p r) (entry : cfg.pc = ResidentColumn.start flatSetup loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    {endAddr : ℕ} (packets : J.Packets endAddr cfg.privateMem) :
    let es := J.trace operands ShrinkCallABI.node pub state mem
    ∃ out, ResidentColumn.Result flatSetup vm M ret flatRow
      (List.finRange (visits party side count sub).length) mem cfg out es ∧
      J.Assembled cfg.privateMem out.privateMem ∧
      SourceTransport.Reads (TerminalLink.workerCell H) es ∧
      DFS.scratch endAddr out.privateMem = J.updated endAddr (DFS.scratch endAddr cfg.privateMem) ∧
      (∀ a : Word w, a.val < endAddr → out.privateMem a = cfg.privateMem a) :=
  native_party_reads J operands ShrinkCallABI.node pub state mem old next M vm inputs loc ret code
    safe (TerminalLink.workerCell H) (J.abi_readSafe degree H terminalRoom old next oldSpace space)
    cfg entry hp hs packets

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
