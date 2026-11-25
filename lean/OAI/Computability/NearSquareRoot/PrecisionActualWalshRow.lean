import OAI.Computability.NearSquareRoot.SynchronizedBoxPhysicalLayout
import OAI.Computability.NearSquareRoot.SynchronizedBoxDecode
import OAI.Computability.NearSquareRoot.SynchronizedRowMembership

/-! # Walsh operator of a row on the emitted directory tape

A block contributes its designated bit precisely when its row cell contains
an opcode. The Walsh operator is self-adjoint, so the stream's direction flag
leaves its selected matrix invariant.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open Matrix
theorem flatWalsh_adjoint {k : ℕ} (b : Finset (Fin k)) : (flatWalsh b)ᴴ = flatWalsh b := by
  classical
  ext x y
  have off : offBits b y x ↔ offBits b x y := ⟨fun h p hp => (h p hp).symm, fun h p hp => (h p hp).symm⟩
  have overlap : physicalOverlap b y x = physicalOverlap b x y := by
    simp only [physicalOverlap,and_comm]
  simp only [conjTranspose_apply,flatWalsh,of_apply,off,overlap]
  split_ifs <;> simp

end BoxFin

namespace ShortFourier.BatchWord
open IntegerMultiplication.Code Matrix SynchronizedBlocks SynchronizedLayers SynchronizedLayers.ScheduleProgram
  SynchronizedPadding BoxFin

noncomputable section

/-- Blocks with a live descriptor in this row of the scheduled tape. -/
def rowActive {k : ℕ} (r : Bool × Row SlotDescriptor) : Finset (Fin ((CoprimeBox.box k).length/4)) :=
  Finset.univ.filter fun j => (readBlock r.2 j.val).isSome

theorem directed_walsh_row {k : ℕ} (hb : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    [∀ i, NeZero (modulus (CoprimeBox.box k) i)] (hd : 4 ≤ (CoprimeBox.box k).length) {dir : Bool}
    {r : Bool × Row SlotDescriptor} (hr : r ∈ directedPlan (dir,tally k))
    (hk : r.2.1 = kindCode .walsh) :
    boxRow (physicalLayout hb) hd r =
      (flatWalsh ((rowActive (k:=k) r).image (selectedPosition hb))).submatrix
        (recordIndex hb) (recordIndex hb) := by
  classical
  let layout := physicalLayout hb
  let active := rowActive (k:=k) r
  have block_eq (j : Fin ((CoprimeBox.box k).length/4)) :
      ((readBlock r.2 j.val).map (fun x => (boxSlot layout j x).matrix (layout.bits j))).getD 1 =
        SynchronizedSelected.block active (numberedBits hb) j := by
    cases he : readBlock r.2 j.val with
    | none => simp [SynchronizedSelected.block,active,rowActive,he]
    | some x =>
      obtain ⟨hm,kind⟩ := directed_read_spec hr j he
      have live : (boxSlot layout j x).kind = .walsh :=
        (boxSlot_kind_of_mem layout hb j hm).trans (kindCode_injective (kind.trans hk))
      have walsh : boxSlot layout j x = .walsh := by
        cases e : boxSlot layout j x <;> simp_all [Slot.kind]
      simp only [Option.map_some, Option.getD_some]
      rw [walsh]
      ext u v
      simp [Slot.matrix,SynchronizedSelected.block,active,rowActive,he,
        blockDiagonal_apply,layout,physicalLayout]
  have base : (rowMatrix (fun j x => (boxSlot layout j x).matrix (layout.bits j)) r.2).submatrix
      (regroup hd _) (regroup hd _) =
      (flatWalsh (active.image (selectedPosition hb))).submatrix (recordIndex hb) (recordIndex hb) := by
    unfold rowMatrix
    simp_rw [block_eq]
    exact numberedWalsh_physical hb hd active
  unfold boxRow
  split_ifs
  · rw [← conjTranspose_submatrix]
    change ((rowMatrix (fun j x => (boxSlot layout j x).matrix (layout.bits j)) r.2).submatrix
      (regroup hd _) (regroup hd _))ᴴ = _
    rw [base,conjTranspose_submatrix,flatWalsh_adjoint]
  · exact base

/-- Matrix at the original ordinal array interface of the physical branch. -/
theorem flat_walshRow {k : ℕ} (hb : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    [∀ i, NeZero (modulus (CoprimeBox.box k) i)] (hd : 4 ≤ (CoprimeBox.box k).length) {dir : Bool}
    (j : Fin (directedPlan (dir,tally k)).length)
    (ht : (directedPlan (dir,tally k))[j.val].2.1 = kindCode .walsh) :
    (boxRow (physicalLayout hb) hd (directedPlan (dir,tally k))[j.val]).submatrix
        (recordIndex hb).symm (recordIndex hb).symm =
      flatWalsh ((rowActive (k:=k) (directedPlan (dir,tally k))[j.val]).image (selectedPosition hb)) := by
  rw [directed_walsh_row hb hd (List.getElem_mem (l:=directedPlan (dir,tally k)) j.isLt) ht]
  ext u v
  simp

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
