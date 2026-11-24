import OAI.Computability.VPVNP.CompressorSurvivingNative
import OAI.Computability.VPVNP.CompressorSurvivingCells

/-!
# Integer readback of the surviving subdivision instruction table

The native masks are division by the same word, yielding zero or one.
They compute both minima needed by a balanced subdivision, even when
the selected supply width is zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingNative

open BurstRAM BurstRAM.PrivateRAM SliceSchedule
open scoped Fin.CommRing

variable {w : ℕ}

private abbrev wd (a : ℕ) : Word w := (a : Word w)

private theorem div_cast {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    BinaryOp.div.eval (wd (w := w) x) (wd y) = wd (x/y) := by
  simp only [BinaryOp.eval,wd,Fin.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy]; rfl

private theorem remainder_cast {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    BinaryOp.mod.eval (wd (w := w) x) (wd y) = wd (x%y) := by
  simp only [BinaryOp.eval,wd,Fin.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy]; rfl

private theorem flag_cast {x : ℕ} (hx : x < 2^w) :
    BinaryOp.div.eval (wd (w := w) x) (wd x) = if x=0 then 0 else 1 := by
  rw [div_cast hx hx]
  split_ifs with h
  · subst x; rfl
  · rw [Nat.div_self (Nat.pos_of_ne_zero h)]; rfl

private theorem piece_pos {b q j : ℕ} (hj : j < q) :
    0 < b/q+(if j < b%q then 1 else 0) ↔ j < min b q := by
  by_cases small : b < q
  · simp only [Nat.div_eq_of_lt small,Nat.mod_eq_of_lt small,min_eq_left small.le,Nat.zero_add]
    split_ifs <;> omega
  · have h := Nat.div_pos (Nat.le_of_not_gt small) (Nat.zero_lt_of_lt hj)
    rw [min_eq_right (Nat.le_of_not_gt small)]; omega

theorem values_exact (r : Row w) (b j : ℕ) (hb : b < 2^w) (hj : j < r.count.val) :
    let d := Data.mk (wd j) r.count (wd b) r.total r.dst
    ∀ f, d.values f = wd (SurvivingCells.value b r.count.val j f) := by
  dsimp only
  let q := r.count.val
  let a := b/q
  let rem := b%q
  let u := if j < rem then 1 else 0
  let k := if b < q then 0 else 1
  let d := Data.mk (wd j) r.count (wd b) r.total r.dst
  have qfit : q < 2^w := r.count.isLt
  have qpos : 0 < q := Nat.zero_lt_of_lt hj
  have eqQ : r.count = wd q := (Fin.natCast_eq_mk ..).symm
  have small : rem < 2^w := (Nat.mod_lt b qpos).trans qfit
  have fitA : a < 2^w := (Nat.div_le_self ..).trans_lt hb
  have d₁ : BinaryOp.div.eval (wd b) r.count = wd a := eqQ ▸ div_cast hb qfit
  have d₂ : BinaryOp.mod.eval (wd b) r.count = wd rem := eqQ ▸ remainder_cast hb qfit
  have add : wd (w := w) j + 1 = wd (j+1) := by simp [wd]
  have quot : BinaryOp.div.eval (wd rem) (wd (w := w) j+1) = wd (rem/(j+1)) := by
    rw [add]; exact div_cast small (Nat.succ_le_of_lt hj |>.trans_lt qfit)
  have mask : BinaryOp.div.eval (wd (w := w) (rem/(j+1))) (wd (rem/(j+1))) = wd u := by
    rw [flag_cast ((Nat.div_le_self ..).trans_lt small)]
    by_cases h : j < rem
    · have hpos := Nat.div_pos (Nat.succ_le_of_lt h) (Nat.succ_pos j)
      simp [u,h,hpos.ne',wd]
    · have hz := Nat.div_eq_of_lt (show rem < j+1 by omega)
      simp [u,h,hz,wd]
  have maskA : BinaryOp.div.eval (wd (w := w) a) (wd a) = wd k := by
    rw [flag_cast fitA]
    by_cases h : b < q
    · simp [a,k,h,Nat.div_eq_of_lt h,wd]
    · have hp := Nat.div_pos (Nat.le_of_not_gt h) qpos
      simp [a,k,h,hp.ne',wd]
  have piece : d.piece = wd (a+u) := by
    change BinaryOp.div.eval (wd b) r.count +
      BinaryOp.div.eval (BinaryOp.div.eval (BinaryOp.mod.eval (wd b) r.count) (wd j+1))
        (BinaryOp.div.eval (BinaryOp.mod.eval (wd b) r.count) (wd j+1)) = _
    rw [d₁,d₂,quot,mask]; simp only [wd,Nat.cast_add]
  have offset : d.offset = wd (j*a + min j rem) := by
    change wd j * BinaryOp.div.eval (wd b) r.count +
      (BinaryOp.mod.eval (wd b) r.count+(wd j-BinaryOp.mod.eval (wd b) r.count)*
      BinaryOp.div.eval (BinaryOp.div.eval (BinaryOp.mod.eval (wd b) r.count) (wd j+1))
        (BinaryOp.div.eval (BinaryOp.mod.eval (wd b) r.count) (wd j+1))) = _
    rw [d₁,d₂,quot,mask]
    by_cases h : j < rem <;> simp [u,h,wd,min_eq_left_of_lt,show ¬ j < rem → rem ≤ j by omega]
  have live : d.live = wd (min b q) := by
    change wd b + (r.count-wd b)*BinaryOp.div.eval (BinaryOp.div.eval (wd b) r.count)
      (BinaryOp.div.eval (wd b) r.count) = _
    rw [d₁,maskA,eqQ]
    by_cases h : b < q <;> simp [k,h,wd,min_eq_left_of_lt,show ¬ b < q → q ≤ b by omega]
  have fitPiece : a+u < 2^w := SurvivingCells.value_fit hb qfit hj (1 : Fin 13)
  have indicator : BinaryOp.div.eval d.piece d.piece = wd (if j < min b q then 1 else 0) := by
    rw [piece,flag_cast fitPiece]
    have pos : 0 < a+u ↔ j < min b q := piece_pos hj
    by_cases hz : a+u=0
    · have hn : ¬ j < min b q := fun h => (Nat.ne_of_gt (pos.mpr h)) hz
      simp [hz,hn,wd]
    · have hp := pos.mp (Nat.pos_of_ne_zero hz)
      rw [ite_eq_right hz,ite_eq_left hp]; rfl
  intro f
  change d.values f = wd (SurvivingCells.value b q j f)
  fin_cases f <;> first | exact piece | exact live | exact indicator | exact offset | rfl

theorem addresses_exact (r : Row w) (b j : ℕ) (hbank : r.bank = r.total+1) :
    let d := Data.mk (wd j) r.count (wd b) r.total r.dst
    ∀ f, d.addresses f = wd (SurvivingCells.address r j f) := by
  intro d f
  have bank : r.total+1 = (r.bank.val : Word w) := hbank.symm.trans (by simp)
  fin_cases f <;> simp [d,Data.addresses,SurvivingCells.address,frameHead,wd,bank] <;> ring

end CompressorRecords.ShrinkSliceSweep.SurvivingNative

end VPVNP
end Computability
end OAI
