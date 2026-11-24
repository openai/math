import OAI.Computability.VPVNP.PairShrinkSurvivingOperands
import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentAddress
import OAI.Computability.VPVNP.CompressorSlotCoreAccess

/-!
# Inverse slot-table lookup at a surviving subdivision

The inverse array published by the shrinking slot construction keeps the
orientation in the middle of each rectangular slot number. The site is the
absolute endpoint of the selected arc, including its remaining lane.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingRect

open BurstRAM Compression Compression.State Compression.PackingData Compression.ShrinkEnergy
open Compression.ShrinkMotif
open CompressorRecords CompressorRecords.Slots CompressorRecords.SlotLevel
open CompressorRecords.SlotSchedule CompressorRecords.ShrinkSlots
open CompressorRecords.PortRefresh.ArgumentAddress ShrinkSurvivingOperands

variable {a b g w : ℕ} {δ : ℝ} (X : State a (packingLaneBits a g))
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (layout : Bool)
variable (width : X.packingData.Motif → Fin 4 → ℕ)
local notation "s" => levelShape (b := b) X
local notation "sub" => Shape.subdivisions (levelShape (b := b) X)
local notation "I" => X.shrinkStateIndex ready layout
local notation "Y" => X.shrinkOutputState layout sub width (I)
local notation "tags" => bitWordFinEquiv (packingTagBits (2 ^ a))
local notation "lanes" => bitWordFinEquiv g

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

variable (m : X.packingData.Motif) (t : Fin 4) (dir : Bool)
variable (j : Fin ((levelShape (b := b) X).subdivisions t))

private theorem site_index_eq (u : Site X.Base (BitWord (packingTagBits (2 ^ a))) (BitWord g)) :
    (siteIndex X.baseIndex tags lanes u).val = siteOrdinal (Y) (packedSiteEquiv u) := by
  let J := 2 ^ packingTagBits (2 ^ a)
  let n := 2 ^ g
  let v := (X.baseIndex u.1).val
  let k := (tags u.2.1).val
  let l := (lanes u.2.2).val
  change l + n * k + J * n * v = (k + J * v) * n + l
  ring

/-- Read the inverse table at the physical candidate-field identifier.
The two fields of each genuine arc have consecutive identifiers. -/
theorem read_val (h : Heads) (mem : Memory w)
    (tables : Build.OrderedTables X ready layout h mem)
    (rectFit : owners s * (s).newDegree ≤ 2 ^ w) :
    let idx := arcAddress X.packingData sub X.baseIndex tags lanes (pad s) (.inl ⟨t, m, j⟩)
    let side : ℕ := if dir then 1 else 0
    (mem (inverseHead s h + (2 * idx.val + side))).val =
      siteOrdinal (Y) (site X layout m t dir) * 2 * 2 ^ b + side * 2 ^ b +
        (slot X layout sub width (I) m t dir j).val := by
  intro idx side
  let i : ActualId X.packingData sub (pad s) := .inl ⟨t, m, j⟩
  let e : Fin 2 := if dir then 1 else 0
  let D := slotDirectory X.packingData sub X.baseIndex tags lanes layout (pad := pad s)
  let hD := fun v ↦ (slotDirectory_degree X.packingData sub X.baseIndex tags lanes
    (two_le_packingColors a) layout v).trans (Nat.add_sub_of_le ready.degree_budget)
  let rank := (sortedFields D (2 ^ b) hD (i, e)).val
  have eSide : e.val = side := by cases dir <;> rfl
  have addr : (D.address (i, e)).val = 2 * idx.val + side := by
    change e.val + 2 * idx.val = _
    rw [eSide, Nat.add_comm]
  rw [← addr, tables.byField, Fin.val_ofNat, Nat.mod_eq_of_lt
    ((sortedFields D (2 ^ b) hD (i, e)).isLt.trans_le rectFit)]
  have sorted := rectangular_slot X.packingData sub X.baseIndex tags lanes (two_le_packingColors a)
    (orderedDyadicPacking_validTags X.slots X.baseIndex) layout ready.degree_budget
    (Nat.one_lt_two_pow (Nat.succ_pos _).ne') i e
  let z := paddedBaseId X.packingData sub i
  let pos := actualEnd X.packingData sub tags layout dir i
  have place : packedSiteEquiv pos = site X layout m t dir := by cases dir <;> rfl
  have which : ((if e = 1 then (I).incoming else (I).outgoing) z).2 =
      slot X layout sub width (I) m t dir j := by
    cases dir with
    | false => rfl
    | true =>
      change ((I).incoming z).2 = ((I).graph.base.target ((I).outgoing z)).2
      exact congrArg Prod.snd ((I).match_eq z).symm
  have owner : (D.owner (i, e)).val = side + 2 * siteOrdinal (Y) (site X layout m t dir) := by
    have test : decide (e = 1) = dir := by cases dir <;> rfl
    change e.val + 2 * (siteIndex X.baseIndex tags lanes
      (actualEnd X.packingData sub tags layout (decide (e = 1)) i)).val = _
    rw [test, site_index_eq X ready layout width, eSide, place]
  change rank = _
  change rank = ((if e = 1 then (I).incoming else (I).outgoing) z).2.val +
    2 ^ b * (D.owner (i, e)).val at sorted
  rw [sorted, which, owner]
  ring

end PairSimulation.ShrinkSurvivingRect

end VPVNP
end Computability
end OAI
