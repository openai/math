import OAI.Computability.VPVNP.PairShrinkPhysicalSourceBounds
import OAI.Computability.VPVNP.PairShrinkCallABI
import OAI.Computability.VPVNP.PairShrinkPartyOutputHeader

/-!
# The resident job at a physical shrinking substep

The old and new DFS layers determine the actual child and parent nodes.
The private arena and hidden scratch come from the terminal geometry. The
producing substep determines the three external table bases for term records,
AB intervals and surviving intervals.
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
local notation "first" => tableBase L cur (1 : Fin 6)
local notation "width" => tableBase L cur (2 : Fin 6)
local notation "slots" => tableBase L cur (3 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "stride" => (10 : Word w)
local notation "shape" => levelShape (b := b i) X
local notation "role" => SelectedArena.roleBase X term stride
local notation "heads" => ShrinkOutput.heads shape role slots
local notation "Z" => ShrinkInput.plan X cut
local notation "absHead" => ShrinkBundlePlan.absoluteHead Z w
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "side" => selectedLayout X B.shrink sel
local notation "Y" => X.shrinkNext B.shrink ready sel
local notation "site" => X.packingData.shrinkPartySite side m party
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "split" => ShrinkOutput.splitBank (b := b i) X B.shrink sel term
  (Fin.val stride) role width
local notation "bank" => selectedAllocation B.shrink X sel term 10 width
  (SlotLevel.Shape.subdivisions shape)

variable (sp : ShrinkResidentSources.Bounds B i X base positions blocks cur)
/-- Classical equality on input base vertices for the selected party's canonical allocation and
old-site ordinals. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

include sp in
private theorem rank_room : (Z).stop < 2 ^ w := by
  have h := (ShrinkInput.range_bounds X cut).2.2.2
  exact h.trans_lt ((Nat.le_add_right ..).trans_lt
    ((Nat.le_add_right ..).trans_lt sp.termRoom))

/-- The popped parent address is the row of this exact party in the new layer. -/
noncomputable def job (n rowEnd older later : ℕ) (old : ShrinkCallDemandCells.Old X side m party)
    (parent : (Y).network.Half site) : ShrinkPartyNative.Job X B.shrink ready sel m party w :=
  let G := TerminalLayout.privateRegions (slotDegree S) n rowEnd (Fintype.card B.Entry)
  let geom := ShrinkCallHeader.geometry X T cut (rank_room B i X base positions blocks cur sp)
  ⟨old, parent, G.arguments,
    later + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal (Y) site,
    ShrinkCallHeader.scratch X (ShrinkCallABI.hiddenBase G n) (n ^ 2) G.histBase,
    older, B.recordLimit + 2, first, term, 10, width, geom.arcFit, geom.bucketFit⟩

/-- Runtime fit and the identity of the physical interval bank recorded by
the producing slot sweep. -/
structure Geometry : Prop where
  rank : (Z).stop < 2 ^ w
  ab : ShrinkABSliceTable.Layout (ShrinkInput.thickBank X T cut) (ShrinkInput.piecesBank X T cut)
    (Z).B ns nt first
  split_eq : split = bank
  allocation : (bank).Fits
  absolute : (absHead).val + idx < 2 ^ w
  slot : finish shape heads < 2 ^ w
  degree : 2 ^ b i < 2 ^ w
  two : 2 < 2 ^ w
  lanes : 2 ^ g < 2 ^ w
  capacity : Fintype.card (Y).Base * 2 ^ g * 2 ^ b i ≤ 2 ^ w
  termBefore : ShrinkInput.termEnd X cut 10 ≤ endAddress L
  absoluteBefore : (absHead).val + ShrinkTermInputs.motifCount X ≤ endAddress L
  intervalsBefore : (bank).last ≤ endAddress L

include sp in
/-- Derive every fit from the physical source extents. In particular the
`max` in the producing sweep's allocator equals the address in table two. -/
theorem geometry : Geometry B i X ready sel m base positions blocks cur := by
  have nextEnd : levelStart L (cur + 1) ≤ endAddress L := levelStart_mono L sp.nextLive.le
  have table (j : Fin 6) : tableBase L cur j ≤ endAddress L :=
    (Nat.le_add_right ..).trans ((tableEnd_le_nextLevel L cur j).trans nextEnd)
  have headerEnd : levelStart L cur + 66 ≤ endAddress L := by
    apply le_trans _ nextEnd
    change levelStart L cur + levelHeaderWords L ≤ levelStart L (cur + 1)
    simp only [levelStart, Nat.succ_mul, levelWords]
    omega
  have ten : 10 < 2 ^ w := by have := sp.room; omega
  have stepVal : (10 : Word w).val = 10 := Nat.mod_eq_of_lt ten
  have termBefore := sp.termBefore.trans (table 1)
  have ab := BlockSlices.ab_layout i X T cut sp.termRoom sp.fresh
    (sp.widthAfter.trans_lt ((table 2).trans_lt sp.room))
  have widthAfter := (Nat.le_add_right first _).trans sp.widthAfter
  have low := sp.selectedBefore.trans widthAfter
  have weq := ShrinkOutput.width_at_eq i X term stride width low
  have bankEq : split = bank := by
    unfold ShrinkOutput.splitBank
    rw [weq, stepVal]
  have alloc := ShrinkOutput.fits (b := b i) X B.shrink sel term (Fin.val stride) role width
    ready stepVal.ge sp.packedRoom
  have last : (bank).last ≤ endAddress L := by
    rw [← bankEq, ShrinkOutput.splitBank_last]
    exact sp.slotAfter.trans (table 3)
  have rank := rank_room B i X base positions blocks cur sp
  have lane := (Z).scalarFits Fintype.card_pos rank
  have absEarly : (absHead).val + ShrinkTermInputs.motifCount X ≤ (Z).ranks := by
    rw [ShrinkTermSelection.motifCount_eq X]
    change ((Z).gathered + (Z).B * (Z).Q) % 2 ^ w + (Z).B * (Z).Q ≤ (Z).gathered + _
    have h := Nat.add_le_add_right (Nat.mod_le ((Z).gathered + (Z).B * (Z).Q) (2 ^ w))
      ((Z).B * (Z).Q)
    exact h.trans_eq (by change _ = (Z).gathered + (2 * (Z).B) * (Z).Q; ring)
  have rankBefore : (Z).ranks ≤ endAddress L :=
    (Nat.le_add_right ..).trans ((ShrinkInput.range_bounds X cut).2.2.2.trans
      (sp.fresh.trans (table 1)))
  have absBefore := absEarly.trans rankBefore
  have ordinal : idx < ShrinkTermInputs.motifCount X := ((ShrinkMotifOrder.entries X).symm m).isLt
  let next : Fin (L).levels := ⟨cur + 1, sp.nextLive⟩
  have nextFit := packed_incidence_room L sp.room next sp.nextCapacity
  have cap : Fintype.card (Y).Base * 2 ^ g * 2 ^ b i < 2 ^ w := by
    rw [(next_counts X B.shrink ready sel).2]
    omega
  have degreeFit := (Nat.le_mul_of_pos_left (2 ^ b i)
    (Nat.mul_pos (Fintype.card_pos (α := (Y).Base)) (Nat.two_pow_pos g))).trans_lt cap
  exact ⟨rank, ab, bankEq, bankEq ▸ alloc, (Nat.add_lt_add_left ordinal _).trans
    (absBefore.trans_lt sp.room), sp.slotRoom, degreeFit, by omega, lane.2.2.2.2.1, cap.le,
    termBefore, absBefore, last⟩

end PairSimulation.ShrinkCanonicalJob

end VPVNP
end Computability
end OAI
