import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorShrinkBundleFrame

/-! # Resident inputs for the block's AB calendar

The term scan preserves the six earlier demand columns. The selected
placement and preimage passes write above those columns. Any intervening
hidden-map passes that preserve the input prefix thus leave all source
records required by the two interval calendars in their original cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif MotifBlocks MotifGrid
open BurstRAM ShrinkSliceSweep ShrinkBlockInputs SlotLevel ShrinkSlots
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
variable (sel : SelectedScore.Selection B X) (term stride abs : Word w) (T : IncidenceDirectory w) (start : ℕ)

local notation "role" => SelectedArena.roleBase X term stride
local notation "keepEnd" => SelectedFinish.stop X term stride
local notation "origin" => SelectedArena.origin X term stride
local notation "sh" => levelShape (b := b i) X

set_option maxHeartbeats 1600000 in
/-- Transport the rows written by the selected geometry across the subsequent
prefix-preserving passes, with the original demand and absolute-ID tables. -/
theorem resident_from_geometry (width : ℕ) (selectors : Word w) (p₀ : Fin 14 → Word w) (termMem input : Memory w)
    (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w) (wide : 10 ≤ stride.val)
    (chosen : SelectedFinish.Built B X term stride selectors p₀ sel termMem p q)
    (hiddenFrame : ∀ x < keepEnd, input x = q.final (p.final termMem) x)
    (demand : DemandWidths.Stored X.packingData (Shrink.packedIndex X.baseIndex) X.packingWidth
      X.shrinkOrder X.shrinkNumber (ShrinkInput.thickBank X T start) (ShrinkInput.cdBank X T start)
      (ShrinkInput.piecesBank X T start) input)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs input) :
    Resident B i X sel term stride abs T start width input := by
  let placed := q.final (p.final termMem)
  have hbound := old_bounds i X term stride
  refine ⟨demand,directory,?_,?_,?_,?_⟩
  · have src := resident_terms (b := b i) B X term stride selectors role width sel placed chosen.terms
    apply terms_after B.shrink X term stride.val _ (sh).subdivisions sel placed input src
    intro j r hr base
    have startLe : base.val ≤ term.val+j.val*stride.val := Nat.mod_le ..
    have rowLe := Nat.mul_le_mul_right stride.val j.isLt
    rw [Nat.succ_mul] at rowLe
    change j.val*stride.val+stride.val ≤ motifCount X*stride.val at rowLe
    exact hiddenFrame _ ((show base.val+r < term.val+motifCount X*stride.val by omega).trans_le hbound.1)
  · have keep (arc) (j : ℕ) (hj : j < 4) : input (role+4*(DemandRAM.absoluteIndex X arc).val+j) = placed (role+4*(DemandRAM.absoluteIndex X arc).val+j) := by
      have hi : (DemandRAM.absoluteIndex X arc).val < absoluteCount X := (DemandRAM.absoluteIndex X arc).isLt
      exact hiddenFrame _ (by omega)
    constructor
    · intro arc; rw [keep arc 3 (by decide)]; exact chosen.roles.cd arc
    · intro arc r; rw [keep arc (SlotOwners.roleOffset r) (by cases r <;> decide)]; exact chosen.roles.packed arc r
  · exact (hiddenFrame _ hbound.2.2).trans chosen.chosenCell
  · exact preimages_retained X term stride chosen.raw.directory hiddenFrame

set_option maxHeartbeats 1600000 in
/-- The verified term pass, the selected geometry and the intervening
memory frame supply the actual resident inputs for `withAB`. -/
theorem resident_of_selected (width : ℕ) (selectors : Word w) (p₀ : Fin 14 → Word w) (termMem input : Memory w)
    (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w)
    (hterm : term = ShrinkInput.termHead X start) (wide : 10 ≤ stride.val)
    (termRoom : ShrinkInput.termEnd X start stride.val < 2^w)
    (retained : ShrinkInput.Retained X T start termMem)
    (chosen : SelectedFinish.Built B X term stride selectors p₀ sel termMem p q)
    (hiddenFrame : ∀ x < keepEnd, input x = q.final (p.final termMem) x)
    (absEarly : abs.val+motifCount X ≤ origin)
    (absolute : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber abs termMem) :
    Resident B i X sel term stride abs T start width input := by
  have hbound := old_bounds i X term stride
  have originEarly : origin ≤ keepEnd := by omega
  have early (x : ℕ) (hx : x < origin) : input x = termMem x :=
    (hiddenFrame x (hx.trans_le originEarly)).trans (chosen.frame x (.inl hx))
  have layout := ShrinkInput.termLayout X T start stride.val termRoom
  have headBefore : (ShrinkInput.demandHead (w := w) X start).val ≤ origin := by
    have sep := layout.2.2.1
    rw [← hterm] at sep
    unfold SelectedArena.origin
    omega
  apply resident_from_geometry B i X sel term stride abs T start width selectors p₀ termMem input
    p q wide chosen hiddenFrame (ShrinkDemandFrame.retain retained.stored layout.2.1
      (fun x hx => early x (hx.trans_le headBefore)))
  intro j
  exact (congrArg Fin.val (early _ ((Nat.add_lt_add_left j.isLt _).trans_le absEarly))).trans (absolute j)

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
