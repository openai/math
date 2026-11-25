import OAI.ThreeFlat.RAM.GuardedDescriptorAddress
import OAI.ThreeFlat.RAM.GuardedRecord

namespace OAI
/-! # Identifying a guarded descriptor with the encoded tensor network row -/

namespace ThreeFlat.RAM.GuardedDescriptor

open Computability.VPVNP.BurstRAM Diagonal Diagonal.GuardedNetwork BitLayout
open scoped Fin.CommRing

variable {F : Type*} [CommSemiring F] {w p q b e t : ℕ}

structure Readers (w : ℕ) where
  copy : Word w → Word w → Word w → Word w
  pin : Word w → Word w → Word w
  left : Word w → Word w → Word w
  right : Word w → Word w → Word w

/-- The four callback contracts refer to the original record and the three
families of actual source addresses used to assemble the network. -/
structure Reads (R : Readers w) (N : BitNetwork F q) (input : Fin t → Fin q → BitSource b p)
    (left right : Fin t → Fin e → BitSource b p) (code : FieldCode F w) : Prop where
  copy : ∀ (i : Fin t) (u : Fin N.cells) (j : Fin 11),
    R.copy (i.val : Word w) (u.val : Word w) (j.val : Word w) = record N code u j
  pin : ∀ (i : Fin t) (j : Fin q),
    R.pin (i.val : Word w) (j.val : Word w) = (sourceAddress (input i j) : Word w)
  left : ∀ (i : Fin t) (j : Fin e),
    R.left (i.val : Word w) (j.val : Word w) = (sourceAddress (left i j) : Word w)
  right : ∀ (i : Fin t) (j : Fin e),
    R.right (i.val : Word w) (j.val : Word w) = (sourceAddress (right i j) : Word w)

def recordInputs (N : BitNetwork F q) (code : FieldCode F w) (p b e base address : ℕ) :
    Inputs (Word w) :=
  ⟨address,base,q,N.cells,N.internal,e,p,b,code.encode 0,code.encode 1⟩

private theorem cast_lt_iff {m n : ℕ} (hm : m < 2^w) (hn : n < 2^w) :
    (m : Word w) < (n : Word w) ↔ m < n := by
  change (m : Word w).val < (n : Word w).val ↔ _
  rw [Fin.val_cast_of_lt hm, Fin.val_cast_of_lt hn]

private theorem cast_eq_iff {m n : ℕ} (hm : m < 2^w) (hn : n < 2^w) :
    (m : Word w) = (n : Word w) ↔ m = n := by
  rw [Fin.ext_iff,Fin.val_cast_of_lt hm,Fin.val_cast_of_lt hn]

omit [CommSemiring F] in
private theorem recode_source (N : BitNetwork F q) (input : Fin t → Fin q → BitSource b p)
    (pin : Word w → Word w → Word w) (i : Fin t) (s : BitSource N.internal q)
    (hp : ∀ j : Fin q, pin (i.val : Word w) (j.val : Word w) = (sourceAddress (input i j) : Word w))
    (fits : 2+q+N.internal < 2^w) :
    let raw := (sourceAddress s : Word w)
    (if raw < 2 then raw else if raw < 2+(q : Word w) then pin (i.val : Word w) (raw-2)
      else 2+(p : Word w)+(b : Word w)+(i.val : Word w)*(N.internal : Word w)+
        (raw-(2+(q : Word w)))) = (GuardedRecord.mapped N input i s : Word w) := by
  have h2 : 2 < 2^w := by omega
  have hw : 2+q < 2^w := by omega
  have castStart : (2 : Word w)+(q : Word w) = ((2+q : ℕ) : Word w) := by push_cast; rfl
  cases s with
  | constant v =>
    change (if (v.toNat : Word w) < 2 then _ else _) = _
    have vlt : v.toNat < 2 := by cases v <;> decide
    have hv : (v.toNat : Word w) < 2 := (cast_lt_iff (vlt.trans h2) h2).2 vlt
    rw [ite_eq_left hv]
    rfl
  | pin j =>
    let a := 2+j.val
    have hraw : a < 2^w := by dsimp [a]; omega
    have nonconst : ¬ (a : Word w) < 2 := (cast_lt_iff hraw h2).not.mpr (by dsimp [a]; omega)
    have oldPin : (a : Word w) < (2 : Word w)+q := by
      rw [castStart,cast_lt_iff hraw hw]; dsimp [a]; omega
    change (if (a : Word w) < 2 then _ else if (a : Word w) < 2+q then _ else _) = _
    rw [ite_eq_right nonconst,ite_eq_left oldPin]
    have idx : (a : Word w)-2 = (j.val : Word w) := by dsimp [a]; push_cast; abel
    change pin _ ((a : Word w)-2) = _
    rw [idx]
    exact hp j
  | hidden j =>
    let a := 2+q+j.val
    have hraw : a < 2^w := by dsimp [a]; omega
    have nonconst : ¬ (a : Word w) < 2 := (cast_lt_iff hraw h2).not.mpr (by dsimp [a]; omega)
    have oldHidden : ¬ (a : Word w) < (2 : Word w)+q := by
      rw [castStart,cast_lt_iff hraw hw]; dsimp [a]; omega
    change (if (a : Word w) < 2 then _ else if (a : Word w) < 2+q then _ else _) = _
    rw [ite_eq_right nonconst,ite_eq_right oldHidden]
    dsimp [GuardedRecord.mapped,sourceAddress,a,hiddenBase]
    push_cast
    ring

variable (N : BitNetwork F q) (input : Fin t → Fin q → BitSource b p)
  (left right : Fin t → Fin e → BitSource b p) (code : FieldCode F w)
  (R : Readers w) (hR : Reads R N input left right code)

include hR

theorem word_copied_record (base : ℕ) (i : Fin t) (u : Fin N.cells) (j : Fin 11)
    (sourceFit : 2+q+N.internal < 2^w) (widthFit : N.cells+e < 2^w) (h11 : 11 < 2^w)
    (fit : recordAddress base N.cells e i.val u.val j.val < 2^w) :
    let a := recordAddress base N.cells e i.val u.val j.val
    let P := recordInputs N code p b e base a
    word P R.copy R.pin R.left R.right =
      record (network N input left right) code (finProdFinEquiv (i,u.castAdd e)) j := by
  let a := recordAddress base N.cells e i.val u.val j.val
  let P := recordInputs N code p b e base a
  let c := coordinates (wordOps w) P
  have hi : u.val < N.cells+e := by omega
  obtain ⟨hblock,hcell,hcol,_⟩ := coordinates_record P base N.cells e i.val u.val j.val
    rfl rfl rfl rfl j.isLt hi widthFit h11 fit
  have hc : c.localCell < P.oldCells := by
    change (coordinates (wordOps w) P).localCell < (N.cells : Word w)
    rw [hcell,cast_lt_iff (hi.trans widthFit) (by omega)]
    exact u.isLt
  change finish (wordOps w) P c _ _ _ _ = _
  rw [finish_copy _ _ _ _ _ _ hc,GuardedRecord.copied_record]
  dsimp only [c]
  rw [hcol,hblock,hcell,hR.copy]
  have hcmp : (j.val : Word w) < 3 ↔ j.val < 3 := cast_lt_iff (m:=j.val) (n:=3) (j.isLt.trans h11) (by omega)
  by_cases hj : j.val < 3
  · rw [ite_eq_left (hcmp.mpr hj),dite_eq_left hj]
    rw [show record N code u j = (sourceAddress (N.source u ⟨j.val,hj⟩) : Word w) by
      simp [record,hj]]
    exact recode_source N input R.pin i _ (hR.pin i) sourceFit
  · rw [ite_eq_right (hcmp.not.mpr hj),dite_eq_right hj]

theorem word_guard_record (base : ℕ) (i : Fin t) (u : Fin e) (j : Fin 11)
    (widthFit : N.cells+e < 2^w) (h11 : 11 < 2^w)
    (fit : recordAddress base N.cells e i.val (N.cells+u.val) j.val < 2^w) :
    let a := recordAddress base N.cells e i.val (N.cells+u.val) j.val
    let P := recordInputs N code p b e base a
    word P R.copy R.pin R.left R.right =
      record (network N input left right) code (finProdFinEquiv (i,Fin.natAdd N.cells u)) j := by
  let a := recordAddress base N.cells e i.val (N.cells+u.val) j.val
  let P := recordInputs N code p b e base a
  let c := coordinates (wordOps w) P
  have hi : N.cells+u.val < N.cells+e := by omega
  obtain ⟨hblock,hcell,hcol,hguard⟩ := coordinates_record P base N.cells e i.val (N.cells+u.val)
    j.val rfl rfl rfl rfl j.isLt hi widthFit h11 fit
  have gu : c.guardIndex = (u.val : Word w) := by
    simpa using hguard (by omega)
  have hc : P.oldCells ≤ c.localCell := by
    change (N.cells : Word w) ≤ (coordinates (wordOps w) P).localCell
    rw [hcell]
    exact le_of_not_gt ((cast_lt_iff (hi.trans widthFit) (by omega)).not.mpr (by omega))
  change finish (wordOps w) P c _ _ _ _ = _
  rw [GuardedRecord.guard_record]
  have hstart : c.block = (i.val : Word w) := hblock
  have hcolumn : c.col = (j.val : Word w) := hcol
  by_cases small : j.val < 3
  · rw [finish_guard _ _ _ _ _ _ hc,hcolumn,hstart,gu,hR.left,hR.right]
    have eqw (z : ℕ) (hz : z < 3) : (j.val : Word w) = (z : Word w) ↔ j.val = z :=
      cast_eq_iff (j.isLt.trans h11) (by omega)
    have hz : (j.val : Word w) = 0 ↔ j.val = 0 := eqw 0 (by decide)
    have ho : (j.val : Word w) = 1 ↔ j.val = 1 := eqw 1 (by decide)
    have ht : (j.val : Word w) = 2 ↔ j.val = 2 := eqw 2 (by decide)
    by_cases h0 : j.val = 0
    · rw [ite_eq_left (hz.mpr h0),ite_eq_left h0]
      rfl
    rw [ite_eq_right (hz.not.mpr h0),ite_eq_right h0]
    by_cases h1 : j.val = 1
    · rw [ite_eq_left (ho.mpr h1),ite_eq_left h1]
      rfl
    have h2 : j.val = 2 := by omega
    rw [ite_eq_right (ho.not.mpr h1),ite_eq_right h1,ite_eq_left (ht.mpr h2),ite_eq_left h2]
  · have hj : j.val-3 < 8 := by omega
    have heq : c.col = ((3+(j.val-3) : ℕ) : Word w) := by
      rw [hcolumn,show 3+(j.val-3)=j.val by omega]
    rw [finish_guard_coeff _ _ _ _ _ _ hc (j.val-3) hj heq h11]
    have bits (z : Fin 8) :
        z.val%2 = (z.val/2)%2 ↔ z.val.testBit 0 = z.val.testBit 1 := by
      revert z; decide
    have := bits ⟨j.val-3,hj⟩
    simp only [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : j.val ≠ 1),
      ite_eq_right (by omega : j.val ≠ 2)]
    simp only [this]
    rfl

/-- Every valid word of a guarded cell record equals the specified descriptor
with the stated four source readers. -/
theorem word_record (base : ℕ) (i : Fin t) (u : Fin (N.cells+e)) (j : Fin 11)
    (sourceFit : 2+q+N.internal < 2^w) (widthFit : N.cells+e < 2^w) (h11 : 11 < 2^w)
    (fit : recordAddress base N.cells e i.val u.val j.val < 2^w) :
    let a := recordAddress base N.cells e i.val u.val j.val
    word (recordInputs N code p b e base a) R.copy R.pin R.left R.right =
      record (network N input left right) code (finProdFinEquiv (i,u)) j := by
  induction u using Fin.addCases with
  | left k => exact word_copied_record N input left right code R hR base i k j sourceFit widthFit h11 fit
  | right k => exact word_guard_record N input left right code R hR base i k j widthFit h11 fit

end ThreeFlat.RAM.GuardedDescriptor

end OAI
