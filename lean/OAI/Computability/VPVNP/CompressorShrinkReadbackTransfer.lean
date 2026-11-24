import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables

/-! # Shrinking slice readbacks after later memory writes

The AB endpoint lists, surviving interval descriptors and sparse subdivision
widths lie below the ordered-slot workspace. A subsequent pass that preserves those addresses can read them in its own
terminal memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open BurstRAM Compression Compression.PackingData ShrinkBlockInputs ShrinkSliceSweep SlotLevel ShrinkSlots
open Compression.ShrinkMotif MotifBlocks MotifGrid
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (term stride : Word w)

local notation "sh" => levelShape (b := b i) X
local notation "role" => SelectedArena.roleBase X term stride
local notation "bankAt" => splitBank (b := b i) X B.shrink sel term stride.val role
local notation "sitesOrd" => Shrink.packedIndex (a := a i) (g := g) X.baseIndex
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)

/-- The AB and surviving CD tables of a single selected block, as read from
one physical memory. -/
structure SliceReadbacks (first width : ℕ) (post : Memory w) : Prop where
  abFields : ABFields i X first post
  intervals : ∀ j, Image ((bankAt width).row j)
    (selected X.packingData X.shrinkNumber sitesOrd (bankAt width) B.shrink X.packingWidth sel j) post
  sparseWidths : SlotWidthScan.SplitRows X.packingData (sh).subdivisions X.baseIndex
    (bitWordFinEquiv (Shrink.J (a i))) (bitWordFinEquiv g) (branchWidth X B.shrink sel)
    (widthBase X term.val stride.val role width) post

variable {B i X sel term stride}

/-- Transfer every AB frame and its two endpoint lists through a memory
frame covering the full bundle rectangle. -/
theorem abFields_transfer_interval {T : IncidenceDirectory w} {start first limit : ℕ} {before post : Memory w}
    (h : ABFields i X first before) {termStride : ℕ} (termRoom : ShrinkInput.termEnd X start termStride < 2^w)
    (fresh : ShrinkInput.stop X start ≤ first)
    (endBefore : first+(ShrinkInput.plan X start).B*IndexedStarts.capacity ns nt ≤ limit)
    (fitsLimit : limit < 2^w) (frame : ∀ x, first ≤ x → x < limit → post x = before x) : ABFields i X first post := by
  let layout := BlockSlices.ab_layout i X T start termRoom fresh (endBefore.trans_lt fitsLimit)
  intro bundle
  let ix := BundleLists.portIndex sitesOrd bundle
  let oldRow := ShrinkSliceArrays.thickWidths X.packingData X.shrinkOrder X.packingWidth bundle
  let newRow := ShrinkSliceArrays.abWidths X.packingData X.shrinkNumber X.packingWidth bundle
  have olen : oldRow.length = ns := List.length_ofFn
  have nlen : newRow.length = nt := List.length_ofFn
  apply (h bundle).transfer (input := ShrinkABSliceTable.columns (ShrinkInput.thickBank X T start)
    (ShrinkInput.piecesBank X T start) ix.val)
  · change IndexedStarts.Space _ _ oldRow.length newRow.length
    rw [olen,nlen]
    exact ShrinkABSliceTable.space layout ix
  · intro x hbase hx
    change x < (ShrinkABSliceTable.bank first ns nt ix.val : Word w).val+IndexedStarts.capacity oldRow.length newRow.length at hx
    have baseEq := ShrinkABSliceTable.bank_val layout ix
    change (ShrinkABSliceTable.bank first ns nt ix.val : Word w).val ≤ x at hbase
    rw [baseEq] at hbase
    rw [olen,nlen,baseEq] at hx
    have hi := Nat.mul_le_mul_right (IndexedStarts.capacity ns nt) ix.isLt
    rw [Nat.succ_mul] at hi
    change ix.val*IndexedStarts.capacity ns nt+IndexedStarts.capacity ns nt ≤
      (ShrinkInput.plan X start).B*IndexedStarts.capacity ns nt at hi
    exact frame x (by omega) (by omega)

/-- The prefix-frame form used immediately after the slot construction. -/
theorem abFields_transfer {T : IncidenceDirectory w} {start first limit : ℕ} {before post : Memory w}
    (h : ABFields i X first before) {termStride : ℕ} (termRoom : ShrinkInput.termEnd X start termStride < 2^w)
    (fresh : ShrinkInput.stop X start ≤ first)
    (endBefore : first+(ShrinkInput.plan X start).B*IndexedStarts.capacity ns nt ≤ limit)
    (fitsLimit : limit < 2^w) (frame : ∀ x < limit, post x = before x) : ABFields i X first post :=
  abFields_transfer_interval (T := T) h termRoom fresh endBefore fitsLimit (fun x _ hx => frame x hx)

set_option maxHeartbeats 900000 in
/-- Transfer both kinds of interval tables and the sparse widths from an actual
three-table run through a later copy preserving the addresses before the
ordered-slot workspace. -/
theorem CompleteTables.slice_transfer {δ : ℝ} {ready : Ready (2^(a i)) (Shrink.colors (a i)) (2^(b i)) δ}
    {abs : Word w} {T : IncidenceDirectory w} {start : ℕ} {I : ShrinkABSliceRecipe.Inputs}
    {pub : Fin 5 → Word w} {state : Word w} {ref mem post : Memory w} {first width slotStart cap : ℕ} {r : TablesRun w}
    (h : CompleteTables B i X ready sel term stride abs start I pub state ref first width slotStart cap mem r)
    (termRoom : ShrinkInput.termEnd X start stride.val < 2^w) (fresh : ShrinkInput.stop X start ≤ first)
    (widthAfter : first+(ShrinkInput.plan X start).B*IndexedStarts.capacity ns nt ≤ width)
    (slotAfter : (bankAt width).last ≤ slotStart) (slotRoom : slotStart < 2^w) (wide : 10 ≤ stride.val)
    (packedRoom : stop (b := b i) X term.val stride.val role width < 2^w)
    (frame : ∀ x < slotStart, post x = r.final x) : SliceReadbacks B i X sel term stride first width post := by
  have fit := fits X B.shrink sel term stride.val role width ready wide packedRoom
  have widthRoom := (width_le_slots (b := b i) X term stride.val role width).trans slotAfter
  have abEnd := widthAfter.trans ((retained_room X term stride.val role width).trans widthRoom)
  have sparse := SlotWidthScan.SplitRows.congr_below _ _ _ _ _ h.remainder.construction.widths
    ((Nat.le_add_right _ _).trans slotAfter) frame
  refine ⟨abFields_transfer (T := T) h.abFields termRoom fresh abEnd slotRoom frame,?_,sparse⟩
  intro j
  apply (h.remainder.construction.intervals j).keep
  intro x hx
  exact frame x (lt_of_not_ge fun beyond => hx ((bankAt width).rowOutside fit j x (.inr (slotAfter.trans beyond))))

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
