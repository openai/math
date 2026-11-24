import OAI.Computability.VPVNP.CompressorShrinkReadbackTransfer
import OAI.Computability.VPVNP.CompressorSlotCoreAccess

/-! # Shrinking tables survive writes to the descriptor header

The AB and CD interval lookups use cells between the first slice table and
the ordered-slot workspace. The forward and inverse slot lookups use cells
in the workspace. The two transfers only need agreement on those ranges.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif MotifBlocks MotifGrid
open ShrinkBlockInputs ShrinkSliceSweep SlotLevel ShrinkSlots
open scoped Classical Fin.CommRing

namespace ShrinkOutput

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps}
variable {g w : ℕ} {X : State (a i) (packingLaneBits (a i) g)} {sel : SelectedScore.Selection B X}
variable {term stride : Word w} {first width slotStart : ℕ}

local notation "sh" => levelShape (b := b i) X
local notation "role" => SelectedArena.roleBase X term stride
local notation "alloc" => splitBank (b := b i) X B.shrink sel term stride.val role width
local notation "base" => widthBase X term.val stride.val role width
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)

set_option maxHeartbeats 900000 in
/-- Slice-table readbacks require agreement only from the AB base through
the end of the CD tables. Earlier header or resident cells may be written. -/
theorem SliceReadbacks.transfer_interval {T : IncidenceDirectory w} {start : ℕ} {before post : Memory w} {δ : ℝ}
    (h : SliceReadbacks B i X sel term stride first width before)
    (ready : Ready (2^(a i)) (Shrink.colors (a i)) (2^(b i)) δ)
    (termRoom : ShrinkInput.termEnd X start stride.val < 2^w) (fresh : ShrinkInput.stop X start ≤ first)
    (widthAfter : first+(ShrinkInput.plan X start).B*IndexedStarts.capacity ns nt ≤ width)
    (slotAfter : (alloc).last ≤ slotStart) (slotRoom : slotStart < 2^w) (wide : 10 ≤ stride.val)
    (packedRoom : stop (b := b i) X term.val stride.val role width < 2^w)
    (frame : ∀ x, first ≤ x → x < slotStart → post x = before x) :
    SliceReadbacks B i X sel term stride first width post := by
  have fit := fits X B.shrink sel term stride.val role width ready wide packedRoom
  have room := (width_le_slots (b := b i) X term stride.val role width).trans slotAfter
  have abEnd := widthAfter.trans ((retained_room X term stride.val role width).trans room)
  have lo : first ≤ base := (Nat.le_add_right _ _).trans (widthAfter.trans (retained_room X term stride.val role width))
  refine ⟨abFields_transfer_interval (T := T) h.abFields termRoom fresh abEnd slotRoom frame,?_,?_⟩
  · intro j
    apply (h.intervals j).keep
    intro x hx
    have low : (alloc).widthBase ≤ x := le_of_not_gt fun below => hx ((alloc).rowOutside fit j x (.inl below))
    exact frame x (lo.trans low) (lt_of_not_ge fun beyond => hx ((alloc).rowOutside fit j x (.inr (slotAfter.trans beyond))))
  · intro j
    have bound := SlotWidthScan.splitOffset_lt X.packingData (sh).subdivisions X.baseIndex
      (bitWordFinEquiv (Shrink.J (a i))) (bitWordFinEquiv g) j
    have last : base+(absoluteCount X*4)*(∑ t,(sh).subdivisions t) ≤ slotStart := (Nat.le_add_right _ _).trans slotAfter
    rw [frame _ (lo.trans (Nat.le_add_right _ _)) ((Nat.add_lt_add_left bound base).trans_le last)]
    exact h.sparseWidths j

end ShrinkOutput

namespace ShrinkSlots.Build

variable {a b g w : ℕ} {δ : ℝ} {X : State a (packingLaneBits a g)}
variable {ready : Ready (2^a) (2*2^a+1) (2^b) δ} {side : Bool} {role slotStart : ℕ}

local notation "sh" => levelShape (b := b) X
local notation "h" => ShrinkOutput.heads sh role slotStart

/-- The sorted endpoint and inverse-field tables use addresses inside the
ordered-slot workspace. -/
theorem OrderedTables.transfer_interval {before post : Memory w} (sorted : OrderedTables X ready side h before)
    (frame : ∀ x, slotStart ≤ x → x < finish sh h → post x = before x) : OrderedTables X ready side h post := by
  let tags := bitWordFinEquiv (packingTagBits (2^a))
  let lanes := bitWordFinEquiv g
  let D := SlotSchedule.slotDirectory X.packingData (sh).subdivisions X.baseIndex tags lanes side (pad := pad sh)
  let degree := fun v ↦ (SlotSchedule.slotDirectory_degree X.packingData (sh).subdivisions X.baseIndex tags lanes
    (State.two_le_packingColors a) side v).trans (Nat.add_sub_of_le ready.degree_budget)
  have low : slotStart ≤ rowsHead sh h := by unfold rowsHead ShrinkOutput.heads; dsimp only; omega
  have rect : rowsHead sh h+owners sh*(sh).newDegree ≤ inverseHead sh h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  have extent : inverseHead sh h+fields sh = targetsHead sh h := rfl
  have high : targetsHead sh h ≤ finish sh h := by
    unfold finish widthHead inHead outHead inverseBaseHead stopAddress shiftsHead; omega
  constructor
  · intro e
    have hi : (SlotSchedule.sortedFields D (2^b) degree e).val < owners sh*(sh).newDegree :=
      (SlotSchedule.sortedFields D (2^b) degree e).isLt
    exact (frame (rowsHead sh h+(SlotSchedule.sortedFields D (2^b) degree e).val) (by omega) (by omega)).trans (sorted.bySlot e)
  · intro e
    have hi : (D.address e).val < fields sh := (D.address e).isLt
    exact (frame (inverseHead sh h+(D.address e).val) (by omega) (by omega)).trans (sorted.byField e)

end ShrinkSlots.Build
end CompressorRecords

end

end VPVNP
end Computability
end OAI
