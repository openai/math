import OAI.Computability.VPVNP.CompressorBlockMetadataPackets
import OAI.Computability.VPVNP.CompressorPublishedHeadsRun
import OAI.Computability.VPVNP.PairShrinkPartyNative
import OAI.Computability.VPVNP.PairShrinkCallFamily
import OAI.Computability.VPVNP.PairSimulationLeafScalarStartup
import OAI.Computability.VPVNP.PairTerminalLayout

/-!
# Register operands of a selected shrinking map

The locator keeps the old header and the popped node. After the hidden pass
the shared registers also hold the geometry pointer, histogram and the start
of the scratch beyond the leaf verifier stacks. The resident scan supplies
the selected motif ordinal. All descriptor expressions use these six live
words and the external level metadata.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallABI

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe
open Compression Compression.ShrinkMotif MotifConversion
open scoped Fin.CommRing

variable {w p r : ℕ} (c : Config w p r) (common : Fin 24 ↪ Fin r)


variable {a g : ℕ} (X : State a (packingLaneBits a g)) (m : X.packingData.Motif)
  (degree n rowEnd labels : ℕ) (level : Word w) (mem : Memory w)
local notation "R" => TerminalLayout.privateRegions degree n rowEnd labels

/-- First private address after all stacks of capacity `n^40`. -/
noncomputable def hiddenBase (regions : LeafArena.Regions) (n : ℕ) : ℕ :=
  regions.stackBase + Fintype.card LeafStartup.ScalarPort * n ^ 40

/-- Register readback for the descriptor and both kinds of gather. The node
arena stride and the hidden slot stride are computed from metadata cell 17. -/
theorem live (old : c.reg (common 11) = level)
    (lengthWord : mem (level + 17).val = (n : Word w))
    (motif : (c.reg (common 18)).val = (ShrinkMotifOrder.stateNumber X m).val)
    (hidden : c.reg (common 8) = (hiddenBase R n : Word w))
    (hist : c.reg (common 10) = ((R).histBase : Word w)) :
    ShrinkCallHeader.Live X m (operands degree) (pub c common) (state c common) level mem
      (R).arguments (hiddenBase R n) (n^2) (R).histBase := by
  have len : mem (c.reg (common 11) + 17).val = (n : Word w) := by rw [old, lengthWord]
  refine ⟨old, motif, len, ?_, hidden, ?_, hist⟩
  · change ((2 * degree : ℕ) : Word w) * mem (c.reg (common 11) + 17).val + 1 =
      ((2 * degree * n + 1 : ℕ) : Word w)
    simp only [len, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  · change mem (c.reg (common 11) + 17).val * mem (c.reg (common 11) + 17).val =
      ((n ^ 2 : ℕ) : Word w)
    rw [len, pow_two, Nat.cast_mul]

/-- The surviving half-address expression indexes the popped node from the
locator. Its destination is the same surviving interval used by the map. -/
theorem supply_readback (dir : Bool) (slot : Fin 4) :
    let I := ShrinkPartyNative.supplyInputs (operands degree) node a dir slot
    I.node.eval (pub c common) (state c common) mem = c.reg (common 0) ∧
      I.destination = ((operands degree).inputs a).surviving dir slot := ⟨rfl, rfl⟩

/-- The only external probe in the six live register operands is the
published length at offset 17. -/
theorem operand_reads (D : ℕ → Prop) (inRange : D (c.reg (common 11) + 17).val) :
    let O := operands degree
    let rd := Expr.ReadsFrom D (pub c common) (state c common) mem
    rd O.level ∧ rd O.motif ∧ rd O.arguments ∧ rd O.argumentStride ∧
      rd O.hidden ∧ rd O.slotStride ∧ rd O.hist ∧ rd node := by
  have lengthRead : Expr.ReadsFrom D (pub c common) (state c common) mem
      (operands degree).arguments := ⟨⟨trivial, trivial⟩, inRange⟩
  exact ⟨trivial, trivial, lengthRead, ⟨⟨trivial, lengthRead⟩, trivial⟩, trivial,
    ⟨lengthRead, lengthRead⟩, trivial, trivial⟩

section Metadata

open DescriptorSpace BlockPlanner Schedule
variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (base : Word w) (positions blocks t step : ℕ) (role : BlockMetadata.Role)
  (fields : BlockMetadata.Fields)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "first" => Script.levelsPerBlock scr * t
local notation "head" => levelStart L (first + step)

/-- The third DFS payload word copies the original problem length into
the old-level header actually selected by the locator. -/
theorem length_published {before : Memory w} {oldSites : ℕ} {rs : List (Report w)}
    (installed : BlockMetadata.Published B base positions blocks t step role fields before
      oldSites rs)
    (rows : before (pt).rows.val = (directoryRows L : Word w))
    (firstRoom : levelStart L 0 + 29 < 2 ^ w)
    (initial : before (levelStart L 0 + 29) = (n : Word w)) :
    after before (eventLog rs) (head + 17) = (n : Word w) := by
  have ptr : BlockHeaderPlan.firstHeader.eval (pt).data (levelStart L first : Word w) before =
      (levelStart L 0 : Word w) :=
    BlockHeaderPlan.firstHeader_eval L base before _ (Fin.cast_val_eq_self _).symm rows
  have h := installed.payload 2
  change after before (eventLog rs) (head + 15 + 2) =
    before ((BlockHeaderPlan.firstHeader.eval (pt).data (levelStart L first : Word w) before) +
      (29 : Word w)).val at h
  rw [ptr, ← show ((levelStart L 0 + 29 : ℕ) : Word w) = (levelStart L 0 : Word w) + 29 by simp,
    Fin.val_natCast, Nat.mod_eq_of_lt firstRoom, initial] at h
  simpa only [Nat.add_assoc] using h

end Metadata

/-- The four term and fourteen data-head stores preserve the metadata length
used on entry to the map. -/
theorem length_after_heads (L : DescriptorSpace.Layout) (P : Fin 5 → Word w) (st : Word w)
    (before : Memory w) (head : ℕ) (termDest termValue : Fin 4 → Expr)
    (dataDest dataValue : Fin 14 → Expr)
    (lengthWord : before (head + 17) = (n : Word w))
    (fit : head + 17 < 2 ^ w)
    (term : PublishedHeads.Published L P st before (head + 36) termDest termValue)
    (data : PublishedHeads.Published L P st
      (PublishedHeads.image P st before (head + 36) termValue) (head + 40) dataDest dataValue) :
    PublishedHeads.image P st (PublishedHeads.image P st before (head + 36) termValue)
      (head + 40) dataValue ((head : Word w) + 17).val = (n : Word w) := by
  rw [← show ((head + 17 : ℕ) : Word w) = (head : Word w) + 17 by simp, Fin.val_natCast,
    Nat.mod_eq_of_lt fit]
  exact (data.outside _ (.inl (by omega))).trans
    ((term.outside _ (.inl (by omega))).trans lengthWord)

end PairSimulation.ShrinkCallABI

end VPVNP
end Computability
end OAI
