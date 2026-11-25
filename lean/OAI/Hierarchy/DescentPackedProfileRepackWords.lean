import OAI.Hierarchy.DescentPackedProfileArchive
import OAI.Hierarchy.DescentPackedProfileRepackNative

namespace OAI
/-! # Digits of an original selector shelf at the pitch of an ordinary date -/
namespace Hierarchy.DescentPackedProfileRepack
open DescentSIMDLookup DescentTerminalEpochChart DescentTerminalEpochBits DescentPackedProfileTape
open DescentPackedProfileWindow DescentPackedProfileWide
open ThreeFlat Routing
open scoped Classical Fin.CommRing
noncomputable section

theorem widen_word {P : Type} (entry : Source P) (z : P→Bool) (d B : ℕ)
    (extend : width entry.C≤d) (j : ℕ) :
    widen (width entry.C) d B (packed entry.pin z B j).val=
      (word d B (wideCell entry.pin z d extend) j).val := by
  unfold widen packed word
  rw [Fin.cast_val_eq_self,Equiv.symm_apply_apply]
  apply congrArg Fin.val
  apply congrArg (encode d B)
  funext i
  apply Fin.ext
  exact Fin.val_cast_of_lt ((cell entry.pin z (j*B+i.val)).isLt.trans_le (Nat.pow_le_pow_right (by decide) extend))

theorem row_one {G M : ℕ} (p : Row 1 G M) : (row 1 G M p).val=p.2.val := by
  have alone : p.1=0 := Subsingleton.elim _ _
  simp [row,finProdFinEquiv_apply_val,alone]

theorem actual_data {P : Type} (entry : Source P) (z : P→Bool) {M : ℕ} (p : Row 1 entry.seats M) :
    data (fun (_ : Fin 1) (g : Fin entry.seats)=>cell entry.pin z g.val) p=packed entry.pin z M p.2.val := by
  apply congrArg (encode _ M)
  funext i
  by_cases live : p.2.val*M+i.val<entry.seats
  · simp [live]
  · simp [live,inactive entry.pin z (Nat.le_of_not_gt live)]

theorem chunk_slots (seats A : ℕ) (pos : 0<A) : chunks seats A ≤ slots seats A := by
  change (seats+A-1)/A ≤ seats/A+2
  have small:=(Nat.div_le_div_right (c:=A) (Nat.sub_le (seats+A) 1))
  have shift : (seats+A)/A=seats/A+1 := by simpa using Nat.add_mul_div_right seats 1 pos
  omega

theorem wide_guard {P : Type} (entry : Source P) (z : P→Bool) (d B : ℕ)
    (extend : width entry.C≤d) (pos : 0<B) (j : ℕ) (outside : chunks entry.seats B≤j) :
    word d B (wideCell entry.pin z d extend) j=0 := by
  have cover := CallPool.count_le_batches_mul entry.seats B pos
  have end_ : entry.seats≤j*B :=
    (show entry.seats≤chunks entry.seats B*B by simpa [chunks,Nat.mul_comm] using cover).trans
      (Nat.mul_le_mul_right B outside)
  apply (encode d B).symm.injective
  funext i
  change (encode d B).symm ((encode d B) _) i=_
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  have h:=digit_encode ((encode d B).symm 0) i
  simpa [cell_eq,inactive entry.pin z (by omega : entry.seats≤j*B+i.val),digit] using h

end
end Hierarchy.DescentPackedProfileRepack

end OAI
