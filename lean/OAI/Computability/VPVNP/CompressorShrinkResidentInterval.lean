import OAI.Computability.VPVNP.CompressorShrinkBranchResident
import OAI.Computability.VPVNP.CompressorShrinkScoreOperands
import OAI.Computability.VPVNP.CompressorBlockABSliceFootprint

/-! # Inputs retained in table zero across the hidden and map publications

Publishing six resident-directory heads changes cells in the old level header.
Every input of the two interval calendars is nevertheless in table zero,
from the sorted demand columns through the selected child-directory rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkOutput

open Compression BurstRAM ShrinkBlockInputs ShrinkSliceSweep TermScores SlotLevel ShrinkSlots
open scoped Classical Fin.CommRing
open private columns_after before_width from OAI.Computability.VPVNP.CompressorBlockABSliceFootprint

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (T : IncidenceDirectory w) (start : ℕ)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "ids" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w
local notation "keepEnd" => SelectedFinish.stop X term (10 : Word w)
local notation "role" => SelectedArena.roleBase X term (10 : Word w)
local notation "wb" => ShrinkInput.widthBase X start
local notation "z" => ShrinkInput.plan X start
local notation "t" => ShrinkInput.thickBank X T start
local notation "cd" => ShrinkInput.cdBank X T start
local notation "ab" => ShrinkInput.piecesBank X T start

set_option maxHeartbeats 1400000 in
theorem Resident.above {width : ℕ} {mem out : Memory w}
    (h : Resident B i X sel term 10 ids T start width mem)
    (room : ShrinkInput.termEnd X start 10 < 2^w) (selected : keepEnd ≤ 2^w)
    (same : ∀ x, start ≤ x → out x = mem x) :
    Resident B i X sel term 10 ids T start width out := by
  have termLow := ScorePackets.start_le_term i X start room
  have hwidth := before_width i X start
  have col := columns_after i X T start room
  have q := (z).values T (ShrinkInput.placementBank X T start) Fintype.card_pos
    (show (z).stop < 2^w by change wb < 2^w; change wb+_+_+_+_ < 2^w at room; omega)
  let block := (z).B*(ShrinkRankSpace.Shape.collectBank z w 4).val
  have blockEq : block = (z).B*(z).Q := by dsimp [block]; rw [q.stride]
  have inputFit : wb+6*((z).B*(z).Q)+2*(z).B < 2^w := by
    change wb+6*((z).B*(z).Q)+2*(z).B+_+_ < 2^w at room; omega
  have cd₂ : (cd 2).val = wb+block := by
    change (wb%(2^w)+block)%(2^w) = _
    rw [Nat.mod_eq_of_lt (show wb<2^w by omega),Nat.mod_eq_of_lt (by omega)]
  have cd₃ : (cd 3).val = wb+2*block+block := by
    change (wb+2*block+block)%(2^w) = _
    exact Nat.mod_eq_of_lt (by omega)
  have keep (p i j : ℕ) (hp : start ≤ p) : (out (p+i+j)).val = (mem (p+i+j)).val :=
    congrArg Fin.val (same _ (by omega))
  have rb := ShrinkInput.range_bounds X start
  have gathered : ShrinkInput.rankBase X start ≤ (z).gathered := by
    change ShrinkInput.rankBase X start ≤ ShrinkInput.rankBase X start+_+_+_; omega
  have aEnd : (z).gathered+(z).B*(z).Q ≤ wb := by
    change (z).gathered+(z).B*(z).Q ≤ (z).gathered+((2*(z).B)*(z).Q)+(z).A
    rw [Nat.mul_assoc,two_mul]; omega
  have absRoom : (z).gathered+(z).B*(z).Q < 2^w := by omega
  have absLow : start ≤ (ids).val := by change start ≤ (_:ℕ)%(2^w); rw [Nat.mod_eq_of_lt absRoom]; omega
  have hrole : start ≤ role := by unfold SelectedArena.roleBase SelectedArena.placementBase SelectedArena.origin; omega
  have hcell : start ≤ SelectedArena.origin X term (10 : Word w)+2 := by unfold SelectedArena.origin; omega
  refine ⟨⟨fun b j => (keep _ _ _ col.1).trans (h.demand.thickWidths b j),
    fun b j => (keep _ _ _ (by omega : start ≤ (cd 2).val)).trans (h.demand.cdWidths b j),
    fun b j => (keep _ _ _ col.2.1).trans (h.demand.thickStarts b j),
    fun b j => (keep _ _ _ (by omega : start ≤ (cd 3).val)).trans (h.demand.cdStarts b j),
    ⟨fun b j => (keep _ _ _ col.2.2.1).trans (h.demand.ab.widths b j),
    fun b j => (keep _ _ _ col.2.2.2).trans (h.demand.ab.starts b j)⟩⟩,
    fun j => (congrArg Fin.val (same _ (by omega))).trans (h.directory j),?_,
    ⟨fun arc => (congrArg Fin.val (same _ (by omega))).trans (h.roles.cd arc),
     fun arc r => (congrArg Fin.val (same _ (by omega))).trans (h.roles.packed arc r)⟩,
    (same _ hcell).trans h.chosen,?_⟩
  · apply terms_after B.shrink X term (10 : Word w).val _ (levelShape (b := b i) X).subdivisions sel mem out h.terms
    intro j k _ head
    have rowFit := (ShrinkInput.termLayout X T start 10 room).2.2.2
    have hj : j.val ≤ ShrinkTermInputs.motifCount X := by
      rw [← ShrinkTermRecipe.count_card X]; exact j.isLt.le
    have le : j.val*(10 : Word w).val ≤ ShrinkTermInputs.motifCount X*10 :=
      Nat.mul_le_mul hj (Nat.mod_le 10 (2^w))
    have exactHead : head.val = (term).val+j.val*(10 : Word w).val := Nat.mod_eq_of_lt (by omega)
    exact same _ (by omega)
  · have hl : start ≤ SelectedFinish.countStart X term 10 := by
      unfold SelectedFinish.countStart SelectedArena.endAddr; omega
    have hc : (SelectedFinish.counts X term 10).val = SelectedFinish.countStart X term 10 := by
      apply Nat.mod_eq_of_lt
      have positive : 0 < ShrinkPreimages.newCount X := Nat.mul_pos Fintype.card_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
      unfold SelectedFinish.stop SelectedFinish.rowStart at selected; omega
    have hr : (SelectedFinish.rows X term 10).val = SelectedFinish.rowStart X term 10 := by
      apply Nat.mod_eq_of_lt
      have positive : 0 < ShrinkPreimages.oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
      unfold SelectedFinish.stop at selected; omega
    have rowLow : start ≤ (SelectedFinish.rows X term 10).val := by rw [hr]; unfold SelectedFinish.rowStart; omega
    exact ⟨fun v => (congrArg Fin.val (same _ (by omega))).trans (h.preimages.count v),
      fun v j => (congrArg Fin.val (same _ (by omega))).trans (h.preimages.child v j)⟩

/-- Intervening publications may update the header while preserving every
earlier field within the physical scratch table. -/
theorem resident_of_branch_interval (selectors : Word w) (cap : ℕ) {m : Memory w}
    (p : ShrinkBranch.Prefix X T start cap m)
    (v : ShrinkBranch.Selected B X T start 10 selectors cap m p sel)
    (fit : ShrinkBranch.PrefixFits B X T start 10 cap) (room : ShrinkInput.termEnd X start 10 < 2^w)
    (selected : keepEnd ≤ 2^w) (width : ℕ) (input : Memory w)
    (frame : ∀ x, start ≤ x → x < keepEnd → input x = v.beforeOutput x) :
    Resident B i X sel term 10 ids T start width input := by
  let staged : Memory w := fun x => if x < start then v.beforeOutput x else input x
  have keep (x : ℕ) (hx : x < keepEnd) : staged x = v.beforeOutput x := by
    by_cases early : x < start
    · exact ite_eq_left early
    · exact (ite_eq_right early).trans (frame x (Nat.le_of_not_gt early) hx)
  have initial := resident_of_branch B i X sel T start 10 selectors cap p v fit width staged keep
  exact initial.above B i X sel T start room selected (fun x hx => (ite_eq_right (Nat.not_lt.mpr hx)).symm)

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
