import OAI.Computability.VPVNP.CompressorShrinkSlotPhysicalSpace
import OAI.Computability.VPVNP.CompressorShrinkTablesPhysical
import OAI.Computability.VPVNP.PairShrinkOldTableTransfer

/-!
# Physical extents of a shrinking level's resident sources

Both the input and successor incidence banks fit the descriptor's slot
capacity. The selected term rows end before the AB table. The surviving
and ordered slot tables, and both resident directories, lie before the next
level header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkResidentSources

open BurstRAM Compression CompressorRecords CompressorRecords.DescriptorSpace
open CompressorRecords.ShrinkBlockInputs ShrinkSlots
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
variable (base : Word w) (positions blocks cur : ℕ)

local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "cut" => tableBase lay cur (0 : Fin 6)
local notation "first" => tableBase lay cur (1 : Fin 6)
local notation "width" => tableBase lay cur (2 : Fin 6)
local notation "slots" => tableBase lay cur (3 : Fin 6)
local notation "resident" => tableBase lay cur (5 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "step" => (10 : Word w)
local notation "role" => SelectedArena.roleBase X term step
local notation "shape" => levelShape (b := b i) X
local notation "heads" => ShrinkOutput.heads shape role slots
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)

/-- Address bounds for one physical source level and its copied successor. -/
structure Bounds : Prop where
  nextLive : cur + 1 < (lay).levels
  room : endAddress lay < 2 ^ w
  oldCapacity : IncidenceDirectory.slotCount X ≤ slotCapacity lay
  nextCapacity : actualCount shape ≤ slotCapacity lay
  termBefore : ShrinkInput.termEnd X cut 10 ≤ first
  termRoom : ShrinkInput.termEnd X cut 10 < 2 ^ w
  selectedBefore : SelectedFinish.stop X term step ≤ first
  fresh : ShrinkInput.stop X cut ≤ first
  widthAfter : first + (ShrinkInput.plan X cut).B * IndexedStarts.capacity ns nt ≤ width
  slotAfter : ShrinkOutput.slotsBase X (ShrinkOutput.widthBase X (term).val (step).val role width)
    shape ≤ slots
  packedRoom : ShrinkOutput.stop (b := b i) X (term).val (step).val role width < 2 ^ w
  slotRoom : finish shape heads < 2 ^ w
  residentEnd : (ShrinkResidentLayout.layout X resident).endAddr ≤ levelStart lay (cur + 1)
  slotEnd : finish shape heads ≤ levelStart lay (cur + 1)

variable (round : ℕ)
local notation "here" => (S.steps + 1) * round + i.val

/-- Derive the resident-source bounds from a live block in the actual schedule. -/
theorem bounds (live : round < blocks) (size : X.positions ≤ positions)
    (room : endAddress lay < 2 ^ w) : Bounds B i X base positions blocks here := by
  have next : here + 1 < (lay).levels := by
    change here + 1 < 1 + (S.steps + 1) * blocks
    have rounds := Nat.mul_le_mul_left (S.steps + 1) live
    rw [Nat.mul_succ] at rounds
    have stepBound := i.isLt
    omega
  let level : Fin (lay).levels := ⟨here, by omega⟩
  have oldSize : IncidenceDirectory.slotCount X ≤ slotCapacity lay := by
    have positionsEq : Fintype.card X.Base * 2 ^ packingLaneBits (a i) g = X.positions := by
      simp only [State.positions, Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv _),
        Fintype.card_fin]
    have degree : 2 ^ (a i) ≤ slotDegree S :=
      (Finset.le_sup (f := fun j : Fin (S.steps + 1) ↦ 2 ^ S.degreeExponent j)
        (Finset.mem_univ i.castSucc)).trans (le_max_right ..)
    change Fintype.card X.Base * 2 ^ packingLaneBits (a i) g * 2 ^ (a i) ≤ positions * slotDegree S
    rw [positionsEq]
    exact Nat.mul_le_mul size degree
  have space := ShrinkOutput.table_space B i X base positions blocks round live size room
  obtain ⟨_, newSize, _, _⟩ :=
    ShrinkSlotCalendar.physical_space B i X base.val positions blocks level rfl size room
  obtain ⟨_, termEnd, _, _, _, _, slotEnd, _, residentEnd⟩ :=
    BlockLevelFit.shrink B base.val positions blocks level rfl i X size room
  exact ⟨next, room, oldSize, newSize,
    termEnd.within.trans (tableEnd_le_tableBase lay here (show (0 : Fin 6) < 1 by decide)),
    space.termRoom, space.abAfter, space.fresh, space.widthAfter, space.slotAfter, space.packedRoom,
    space.slotRoom, residentEnd.next, slotEnd.next⟩

variable {B i X base positions blocks cur}
local notation "T" => packedIncidence lay w cur (DemandRAM.oldCount X)
local notation "Z" => ShrinkInput.plan X cut

/-- The three occupied incidence columns, the preliminary placement and the
classifier's rows and ranks all precede table one. A frame from the end of the
level header through that table boundary retains the old map-call inputs. -/
theorem Bounds.oldTables (h : Bounds B i X base positions blocks cur)
    {before out : Memory w} (old : ShrinkCallHeader.OldTables X before T cut)
    (frame : ∀ x, incidenceStart lay cur ≤ x → x < first → out x = before x) :
    ShrinkCallHeader.OldTables X out T cut := by
  let level : Fin (lay).levels := ⟨cur, (Nat.lt_succ_self _).trans h.nextLive⟩
  let n := DemandRAM.oldCount X
  have incRoom : incidenceStart lay cur + 6 * n < 2 ^ w :=
    packed_incidence_room lay h.room level h.oldCapacity
  have incEnd : incidenceStart lay cur + 6 * n ≤ cut := by
    have size := Nat.mul_le_mul_left 6 h.oldCapacity
    change incidenceStart lay cur + 6 * n ≤
      incidenceStart lay cur + 6 * slotCapacity lay + 0 * tableWords lay
    simpa only [Nat.zero_mul, Nat.add_zero] using Nat.add_le_add_left size _
  have range (c : Fin 6) :
      incidenceStart lay cur ≤ ((T).column c).val ∧
      ((T).column c).val + n ≤ incidenceStart lay cur + 6 * n := by
    rw [packed_column]
    have bound := Nat.mul_le_mul_right n c.isLt
    rw [Nat.succ_mul] at bound
    have fit : incidenceStart lay cur + c.val * n < 2 ^ w := by omega
    change incidenceStart lay cur ≤ (incidenceStart lay cur + c.val * n) % (2 ^ w) ∧
      (incidenceStart lay cur + c.val * n) % (2 ^ w) + n ≤ _
    rw [Nat.mod_eq_of_lt fit]
    exact ⟨Nat.le_add_right .., by omega⟩
  obtain ⟨placement, rank, widthEnd, inputEnd⟩ := ShrinkInput.range_bounds X cut
  have rankRoom : (Z).stop < 2 ^ w := by
    have room := h.termRoom
    unfold ShrinkInput.termEnd at room
    exact inputEnd.trans_lt (by omega)
  have start : incidenceStart lay cur ≤ cut := (Nat.le_add_right ..).trans incEnd
  have last : cut ≤ first := (placement.trans (rank.trans (widthEnd.trans inputEnd))).trans h.fresh
  apply old.transfer rankRoom (fun c ↦ ((range (c.natAdd 3)).2.trans_lt incRoom).le)
    (D := fun x ↦ incidenceStart lay cur ≤ x ∧ x < first) (fun x hx ↦ (frame x hx.1 hx.2).symm)
  · intro c z lo hi
    exact ⟨(range (c.natAdd 3)).1.trans lo, hi.trans_le ((range (c.natAdd 3)).2.trans
      (incEnd.trans last))⟩
  · intro z lo hi
    exact ⟨start.trans (placement.trans (rank.trans lo)), hi.trans_le (inputEnd.trans h.fresh)⟩
  · intro z lo hi
    exact ⟨start.trans (placement.trans lo), hi.trans_le (widthEnd.trans (inputEnd.trans h.fresh))⟩

end PairSimulation.ShrinkResidentSources

end VPVNP
end Computability
end OAI
