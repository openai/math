import OAI.Computability.VPVNP.CompressorShrinkResidentInterval
import OAI.Computability.VPVNP.CompressorRecordsShrinkBuild

/-! # Reading the old shrinking tables after later writes

The demand columns, motif IDs, ten term words, placement roles, selected bit
and preimage lists all lie in the interval from table zero's base through the
end of the preimage rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkOutput

open Compression BurstRAM ShrinkBlockInputs ShrinkSliceSweep ShrinkSlots
open scoped Classical Fin.CommRing
open private absolute_room from OAI.Computability.VPVNP.CompressorRecordsShrinkBuild

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (T : IncidenceDirectory w) (start : ℕ)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "step" => (10 : Word w)
local notation "ids" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w
local notation "keepEnd" => SelectedFinish.stop X term step
local notation "role" => SelectedArena.roleBase X term step

set_option maxHeartbeats 1200000 in
theorem Resident.below {width : ℕ} {m out : Memory w} (r : Resident B i X sel term step ids T start width m)
    (room : ShrinkInput.termEnd X start 10 < 2^w) (ten : 10 < 2^w)
    (same : ∀ x < keepEnd, out x = m x) : Resident B i X sel term step ids T start width out := by
  have stepVal : (step).val = 10 := Nat.mod_eq_of_lt ten
  have stepRoom : ShrinkInput.termEnd X start (step).val < 2^w := stepVal ▸ room
  have lim := old_bounds i X term step
  have prior := ShrinkInput.termLayout X T start 10 room
  have termEarly : (term).val ≤ keepEnd := (Nat.le_add_right ..).trans lim.1
  have demandEarly : (ShrinkInput.demandHead (w := w) X start).val ≤ keepEnd :=
    ((Nat.le_add_right ..).trans prior.2.2.1).trans termEarly
  have idEnd := absolute_room X start step stepRoom
  have cell (arc) (j : ℕ) (hj : j<4) : out (role+4*(DemandRAM.absoluteIndex X arc).val+j) = m (role+4*(DemandRAM.absoluteIndex X arc).val+j) := by
    have hi : (DemandRAM.absoluteIndex X arc).val < absoluteCount X := (DemandRAM.absoluteIndex X arc).isLt
    exact same _ (by omega)
  refine ⟨ShrinkDemandFrame.retain r.demand prior.2.1 (fun x hx => same x (hx.trans_le demandEarly)),
    fun j => (congrArg Fin.val (same _ ((Nat.add_lt_add_left j.isLt _).trans_le idEnd))).trans (r.directory j),
    ?_,⟨fun arc => (congrArg Fin.val (cell arc 3 (by decide))).trans (r.roles.cd arc),
      fun arc e => (congrArg Fin.val (cell arc.val (SlotOwners.roleOffset e) (by cases e <;> decide))).trans (r.roles.packed arc e)⟩,
    (same _ lim.2.2).trans r.chosen,preimages_retained X term step r.preimages same⟩
  apply terms_after B.shrink X term (step).val _ (levelShape (b := b i) X).subdivisions sel m out r.terms
  intro j l hl ptr
  have baseBound : ptr.val ≤ (term).val+j.val*(step).val := Nat.mod_le ..
  have endBound := Nat.mul_le_mul_right (step).val j.isLt
  rw [Nat.succ_mul] at endBound
  change j.val*(step).val+(step).val ≤ motifCount X*(step).val at endBound
  exact same _ (by omega)

/-- A frame restricted to the allocated table suffices even when later
publications change cells in the old level header. -/
theorem Resident.interval {width : ℕ} {m out : Memory w} (r : Resident B i X sel term step ids T start width m)
    (room : ShrinkInput.termEnd X start 10 < 2^w) (ten : 10 < 2^w) (fit : keepEnd ≤ 2^w)
    (same : ∀ x, start ≤ x → x < keepEnd → out x = m x) : Resident B i X sel term step ids T start width out := by
  let staged : Memory w := fun x => if x < start then m x else out x
  have keep (x : ℕ) (hx : x < keepEnd) : staged x = m x := by
    by_cases early : x < start
    · exact ite_eq_left early
    · exact (ite_eq_right early).trans (same x (Nat.le_of_not_gt early) hx)
  exact (r.below B i X sel T start room ten keep).above B i X sel T start room fit
    (fun x hx => (ite_eq_right (Nat.not_lt.mpr hx)).symm)

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
