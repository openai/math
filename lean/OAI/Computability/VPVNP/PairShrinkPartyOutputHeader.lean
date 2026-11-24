import OAI.Computability.VPVNP.PairShrinkPartyNative

/-!
# Publishing the surviving-column inputs of a resident shrinking party

The eight endpoint programs share the same incidence, motif, inverse-slot
and interval bases. Only their private destinations differ. Reading the
two level headers therefore supplies the recorded setup for every incident
subdivision of the resident map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.State Compression.PackingData
open Compression.ShrinkMotif Compression.ShrinkEnergy MotifBlocks MotifGrid MotifConversion
open CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.ShrinkSlots
open CompressorRecords.ShrinkSliceSweep
open scoped Fin.CommRing

variable {a b g w : ℕ} {δ factor : ℝ} {K : Type*} [_root_.Field K]
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6} (J : Job X F ready sel m party w)
variable (O : ShrinkCallHeader.Operands) (node : Expr) {pub : Fin 5 → Word w}
variable {state level absolute : Word w} {mem : Memory w} {origin : ℕ} {T : IncidenceDirectory w}
variable (old : J.OldPublished O pub state mem level T origin)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

private theorem cast_val (v : Word w) : (v.val : Word w) = v := by simp

private theorem cell_at (i : ℕ) (fit : level.val + i < 2 ^ w) :
    (level + (i : Word w)).val = level.val + i := by
  calc
    _ = (((level.val + i : ℕ) : Word w)).val := by rw [Nat.cast_add, cast_val]
    _ = _ := Nat.mod_eq_of_lt fit

local notation "idx" => ShrinkMotifOrder.stateNumber X m
local notation "s" => levelShape (b := b) X
local notation "side" => selectedLayout X F sel
local notation "Y" => X.shrinkNext F ready sel

include old in
/-- From the two physical level headers and selected array images, recover all the
publication hypotheses for the compiled party without separate endpoint assumptions. -/
theorem Job.SupplyPublished.of_header (heads : SlotLevel.Heads) (U : IncidenceDirectory w)
    (next layer pitch : ℕ)
    (oldRoom : level.val + 42 < 2 ^ w) (newRoom : next + 59 < 2 ^ w)
    (absoluteAt : mem (level.val + 39) = absolute)
    (nextAt : mem (level.val + 40) = (next : Word w))
    (inverseAt : mem (level.val + 41) = (SlotLevel.inverseHead s heads : Word w))
    (intervalAt : mem (level.val + 42) = (J.allocation.widthEnd : Word w))
    (layerAt : mem (next + 14) = (layer : Word w)) (pitchAt : mem (next + 15) = (pitch : Word w))
    (outAt : mem (next + 57) = U.actualOut) (inAt : mem (next + 58) = U.actualIn)
    (widthAt : mem (next + 59) = U.width)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absolute mem)
    (sorted : Build.OrderedTables X ready side heads mem)
    (absFit : absolute.val + (idx).val < 2 ^ w) (slotFit : finish s heads < 2 ^ w)
    (degreeFit : 2 ^ b < 2 ^ w) (twoFit : 2 < 2 ^ w) (lanesFit : 2 ^ g < 2 ^ w)
    (allocation : J.allocation.Fits)
    (images : ∀ i, Image (J.allocation.row i)
      (selected X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) J.allocation
        F X.packingWidth sel i) mem)
    (incidence : U.ActualColumns (Y) mem)
    (capacity : Fintype.card (Y).Base * 2 ^ g * 2 ^ b ≤ 2 ^ w)
    (nodeWord : node.eval pub state mem = (J.node : Word w)) :
    J.SupplyPublished O node pub state mem heads absolute U layer pitch := by
  have motif : O.motif.eval pub state mem = ((idx).val : Word w) := by
    rw [← old.live.motif]
    exact (cast_val _).symm
  have vertices : mem (level.val + 0) = (Fintype.card X.Base : Word w) := by
    rw [← cell_at 0 (by omega : level.val + 0 < 2 ^ w)]
    exact old.levelData.vertices
  have lane : mem (level.val + 3) = ((2 ^ g : ℕ) : Word w) := by
    rw [← cell_at 3 (by omega : level.val + 3 < 2 ^ w)]
    exact old.levelData.residual
  have laneVal : (mem (level.val + 3)).val = 2 ^ g := by rw [lane]; exact Nat.mod_eq_of_lt lanesFit
  have read (d : Bool) (t : Fin 4) := ShrinkSurvivingSelected.inputs_readback X m heads absolute
    level.val next J.allocation.widthEnd U J.arena layer pitch O.level O.motif O.arguments
    O.argumentStride node ((O.inputs a).surviving d t) (old.live.header.trans (cast_val level).symm)
    motif old.live.arguments old.live.argumentStride oldRoom newRoom vertices laneVal
    absoluteAt nextAt inverseAt intervalAt layerAt pitchAt outAt inAt widthAt
  refine ⟨fun d t ↦ (read d t).1, directory, sorted, absFit, slotFit, degreeFit, twoFit,
    allocation, images, fun d t ↦ (read d t).2.1, incidence, capacity, nodeWord, ?_,
    fun d t ↦ (read d t).2.2⟩
  intro dir t
  have vertexExpr : (O.cell 0).eval pub state mem = (Fintype.card X.Base : Word w) := by
    change mem (O.level.eval pub state mem + 0).val = _
    rw [old.live.header]
    exact old.levelData.vertices
  have laneExpr : (O.cell 3).eval pub state mem = ((2 ^ g : ℕ) : Word w) := by
    change mem (O.level.eval pub state mem + 3).val = _
    rw [old.live.header]
    exact old.levelData.residual
  have count := ShrinkCallHeader.count_eq X O pub state mem vertexExpr laneExpr
  have stage : (O.staging a).eval pub state mem = (J.scratch.staging : Word w) := by
    change O.hidden.eval pub state mem + 4 * (O.count a).eval pub state mem *
      O.slotStride.eval pub state mem = _
    rw [old.live.hiddenBase, old.live.stride, count, ← old.motifCount]
    simp [ShrinkCallFields.Scratch.staging]
  change (O.staging a).eval pub state mem + ((1 + dir.toNat * 4 + t.val : ℕ) : Word w) *
    O.slotStride.eval pub state mem = _
  rw [stage, old.live.stride, ← Nat.cast_mul, ← Nat.cast_add]
  rfl

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
