import OAI.Hierarchy.ProbeStageRecordROM
import OAI.Computability.VPVNP.RAMExecution

namespace OAI
/-! # Address arithmetic for the writable counters, masks and fixed lookup tables -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

def countArea (left : Bool) : Fin 16 := if left then 12 else 13
def maskArea (left : Bool) : Fin 16 := if left then 14 else 15

def counterLocation (h d j : ℕ) (left : Bool) (b : Fin (groupBlocks h d j)) (c : Fin (radix h d)) :=
  region h d j (countArea left)+b.val*radix h d+c.val

def maskLocation (h d j : ℕ) (left : Bool) (b : Fin (groupBlocks h d j))
    (r : MaskIndex (radix h d)) (k : Fin (fieldChunks h)) :=
  region h d j (maskArea left)+b.val*((radix h d)^4*fieldChunks h)+rowCode r*fieldChunks h+k.val

private theorem flatten_lt {n m : ℕ} (i : Fin n) (j : Fin m) : i.val*m+j.val<n*m := by
  exact (Nat.add_lt_add_left j.isLt _).trans_le (by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ i.isLt)

theorem rowCode_lt {B : ℕ} (r : MaskIndex B) : rowCode r<B^4 := by
  have cap := (finProdFinEquiv r).isLt
  change _<B^2*B^2 at cap
  change (finProdFinEquiv r).val<B^4
  rw [show B^4=B^2*B^2 by ring]
  exact cap

theorem count_offset {h d j : ℕ} (hd : 1≤d) (depth : j≤rounds d)
    (b : Fin (groupBlocks h d j)) (c : Fin (radix h d)) :
    b.val*radix h d+c.val < regionSize h d :=
  (flatten_lt b c).trans_le (region_room hd depth).2.2.2.2.1

theorem mask_offset {h d j : ℕ} (hd : 1≤d) (depth : j≤rounds d)
    (b : Fin (groupBlocks h d j)) (r : MaskIndex (radix h d)) (k : Fin (fieldChunks h)) :
    b.val*((radix h d)^4*fieldChunks h)+rowCode r*fieldChunks h+k.val < regionSize h d := by
  let index : Fin ((radix h d)^4) := ⟨rowCode r,rowCode_lt r⟩
  let entry : Fin ((radix h d)^4*fieldChunks h) := ⟨index.val*fieldChunks h+k.val,flatten_lt index k⟩
  have cap := (flatten_lt b entry).trans_le (region_room hd depth).2.2.2.2.2
  simpa only [entry,index,Nat.add_assoc] using cap

theorem occurrence_offset {h d : ℕ} (hd : 1≤d) (c : Fin (radix h d)) (i : ℕ)
    (limit : i<(PackedMask.occurrences (formatAdvice h d).row c).length) :
    c.val*directoryCapacity (radix h d) (stringLength h)+i<regionSize h d :=
  (flatten_lt c ⟨i,limit.trans_le (occurrence_length _ c)⟩).trans_le (padded_directory hd)

theorem region_word {h d j : ℕ} (depth : j<rounds d) (k : Fin 16) {i : ℕ} (inside : i<regionSize h d) :
    region h d j k+i<2^wordBits h d copies := by
  have endi := (Nat.add_lt_add_left inside _).trans_le (region_end h d j k)
  have bound := (output_end h d copies j).trans_lt
    ((phase_in_heap (Nat.succ_le_of_lt depth)).trans_lt (heap_room h d copies))
  omega

theorem mask_counter_disjoint (a b : Bool) : maskArea a ≠ countArea b := by cases a <;> cases b <;> decide

theorem region_address_ne {h d j : ℕ} {a b : Fin 16} {i k : ℕ} (hi : i<regionSize h d)
    (hk : k<regionSize h d) (distinct : a≠b) : region h d j a+i ≠region h d j b+k := by
  have separate {x y : Fin 16} (lt : x<y) {o : ℕ} (small : o<regionSize h d) :
      region h d j x+o<region h d j y :=
    (Nat.add_lt_add_left small _).trans_le (region_separate h d j lt)
  rcases lt_or_gt_of_ne distinct with lt|gt
  · exact ((separate lt hi).trans_le (Nat.le_add_right _ _)).ne
  · exact ((separate gt hk).trans_le (Nat.le_add_right _ _)).ne.symm

theorem add_word {w a b : ℕ} (fit : a+b<2^w) : ((a:Word w)+(b:Word w)).val=a+b := by
  rw [← Nat.cast_add,Fin.val_cast_of_lt fit]

end Hierarchy.ProbeStage.Native

end OAI
