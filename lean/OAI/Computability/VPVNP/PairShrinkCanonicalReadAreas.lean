import OAI.Computability.VPVNP.PairShrinkCanonicalJob
import OAI.Computability.VPVNP.PairShrinkPartyReadAreas
import OAI.Computability.VPVNP.PairShrinkPartyReadBounds
import OAI.Computability.VPVNP.PairShrinkCallABIReads

/-!
# Read bounds of the canonical shrinking job

The old level and its successor lie below the end of the descriptor. Both
native gathers and the selected map writer therefore read below the terminal
controller header. The old header's successor word identifies the next
incidence bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCanonicalJob

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords
open CompressorRecords.DescriptorSpace CompressorRecords.ShrinkBlockInputs
open CompressorRecords.ShrinkSlots CompressorRecords.ShrinkSliceSweep
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} {δ : ℝ} (X : State (a i) (packingLaneBits (a i) g))
variable (ready : Ready (2 ^ a i) (Shrink.colors (a i)) (2 ^ b i) δ)
variable (sel : SelectedScore.Selection B X) (m : X.packingData.Motif) (party : Fin 6)
variable (base : Word w) (positions blocks cur : ℕ)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "cut" => tableBase L cur (0 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "shape" => levelShape (b := b i) X
local notation "role" => SelectedArena.roleBase X term (10 : Word w)
local notation "heads" => ShrinkOutput.heads shape role (tableBase L cur (3 : Fin 6))
local notation "Z" => ShrinkInput.plan X cut
local notation "absHead" => ShrinkBundlePlan.absoluteHead Z w
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "U" => packedIncidence L w (cur + 1) (actualCount shape)
local notation "side" => selectedLayout X B.shrink sel
local notation "Y" => X.shrinkNext B.shrink ready sel
local notation "site" => X.packingData.shrinkPartySite side m party
local notation "level" => levelStart L cur
local notation "next" => levelStart L (cur + 1)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

variable (sp : ShrinkResidentSources.Bounds B i X base positions blocks cur)
variable (J : ShrinkPartyNative.Job X B.shrink ready sel m party w)
local notation "allocated" => selectedAllocation B.shrink X sel term 10
  (tableBase L cur (2 : Fin 6))
  (SlotLevel.Shape.subdivisions shape)

include sp in
/-- All concrete array ends required by the AB and surviving scans and the
map's term descriptors, expressed at the actual terminal header. -/
theorem read_areas (firstBank : J.first = tableBase L cur (1 : Fin 6))
    (intervalBank : J.allocation = allocated) (H : Word w) (mem : Memory w)
    (beforeHeader : endAddress L ≤ H.val)
    (successor : mem (level + 40) = (next : Word w)) :
    J.ABAreas (level : Word w) T cut H.val ∧
      J.SupplyAreas (level : Word w) absHead heads U next H.val mem ∧
      ShrinkInput.termEnd X cut 10 ≤ H.val := by
  have geo := geometry B i X ready sel m base positions blocks cur sp
  have nextLe := (levelStart_mono L sp.nextLive.le).trans beforeHeader
  have oldLe := (levelStart_mono L (Nat.le_succ cur)).trans nextLe
  have oldWord : (level : Word w).val = level := Nat.mod_eq_of_lt (oldLe.trans_lt H.isLt)
  have beyond : levelStart L ((cur + 1) + 1) ≤ H.val :=
    (levelStart_mono L sp.nextLive).trans beforeHeader
  have newInc : incidenceStart L (cur + 1) + 6 * slotCapacity L ≤ H.val := by
    have h := tableEnd_le_nextLevel L (cur + 1) (0 : Fin 6)
    change (incidenceStart L (cur + 1) + 6 * slotCapacity L + 0 * tableWords L) +
      tableWords L ≤ _ at h
    omega
  have head : next + 66 = incidenceStart L (cur + 1) := rfl
  have count := (next_counts X B.shrink ready sel).2
  have col (j : Fin 6) : ((U).column j).val + Fintype.card (Y).Base *
      2 ^ g * 2 ^ b i ≤ H.val := by
    rw [count, packed_column]
    change (incidenceStart L (cur + 1) + j.val * actualCount shape) % 2 ^ w + _ ≤ _
    have bound := Nat.mul_le_mul_right (actualCount shape) j.isLt
    rw [Nat.succ_mul] at bound
    have capacity := Nat.mul_le_mul_left 6 sp.nextCapacity
    exact (Nat.add_le_add_right (Nat.mod_le ..) _).trans (by omega)
  have inv : SlotLevel.targetsHead shape heads ≤ finish shape heads := by
    unfold finish widthHead inHead outHead inverseBaseHead SlotLevel.stopAddress
      SlotLevel.shiftsHead
    omega
  refine ⟨sp.party_abAreas J firstBank nextLe, ?_, geo.termBefore.trans beforeHeader⟩
  exact ⟨by simpa only [oldWord] using successor, by omega, geo.absoluteBefore.trans beforeHeader,
    inv.trans (sp.slotEnd.trans nextLe), col 4, col 5,
    intervalBank.symm ▸ geo.intervalsBefore.trans beforeHeader⟩

end PairSimulation.ShrinkCanonicalJob

end VPVNP
end Computability
end OAI
