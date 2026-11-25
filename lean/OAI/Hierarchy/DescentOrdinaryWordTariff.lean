import OAI.Hierarchy.DescentDateBillVolume
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Whole-word date costs for compiled procedures with genuine instruction tables -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentStaticWordColumn ThreeFlat.RAM PhysicalProcedure

def bitTariff {w : ℕ} (code : Procedure w) (ticks : ℕ) := (ticks+7*names code)*w

theorem bitTariff_seq {w : ℕ} (left right : Procedure w) (t s : ℕ) :
    bitTariff (left.seq right) (t+s)=bitTariff left t+bitTariff right s := by
  simp only [bitTariff,names_seq]
  ring

/-- Word-model instruction text and work are both charged at the full bus width. -/
theorem from_words {w : ℕ} (code : Procedure w) (ticks H G h u ratio clock text : ℕ)
    (positive : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h)
    (runtime : ticks≤clock*words H G h u) (table : names code≤text*words H G h u) :
    bitTariff code ticks≤(2*ratio*(clock+7*text))*volumeBits H G h u := by
  let U:=words H G h u
  calc
    _ ≤ (clock*U+7*(text*U))*(ratio*h) :=
      Nat.mul_le_mul (Nat.add_le_add runtime (Nat.mul_le_mul_left 7 table)) bus
    _ = (ratio*(clock+7*text))*(U*h) := by ring
    _ ≤ (ratio*(clock+7*text))*(2*volumeBits H G h u) :=
      Nat.mul_le_mul_left _ (words_bits H G h u positive wide)
    _ = _ := by ring

/-- An addressed successor can have more host rows and fewer groups than its predecessor.
The rounded lookup directory is charged once for each actual operation. -/
theorem ordinary_rectangle (H G actualH actualG h u hostRate groupRate bill : ℕ) (live : 0<H)
    (hosts : actualH≤H*hostRate) (groups : actualG≤G*groupRate) :
    bill*volumeBits actualH actualG h u ≤ H*h*(bill*(1+hostRate))+
      H*G*(4*bill*hostRate*groupRate*u)+2^(h/2)*h*bill := by
  have first : h≤H*h:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right h live
  unfold volumeBits
  calc
    _ ≤ bill*(H*h+(H*hostRate)*h+4*(H*hostRate)*(G*groupRate)*u+2^(h/2)*h) := by
      gcongr
    _ = _ := by ring

theorem occupied_rectangle (H G actualH actualG h u hostRate groupRate bill : ℕ)
    (occupied : 2^(h/2)≤H) (hosts : actualH≤H*hostRate) (groups : actualG≤G*groupRate) :
    bill*volumeBits actualH actualG h u ≤ H*h*(bill*(2+hostRate))+
      H*G*(4*bill*hostRate*groupRate*u) := by
  have core:=ordinary_rectangle H G actualH actualG h u hostRate groupRate bill
    ((Nat.two_pow_pos _).trans_le occupied) hosts groups
  have rom:=Nat.mul_le_mul_right bill (Nat.mul_le_mul_right h occupied)
  calc
    _ ≤ _ :=core
    _ ≤ H*h*(bill*(1+hostRate))+H*G*(4*bill*hostRate*groupRate*u)+H*h*bill :=
      Nat.add_le_add_left rom _
    _ = _ := by ring

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
