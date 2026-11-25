import OAI.ThreeFlat.RAM.HistoryJoinScan
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Abel

namespace OAI
/-! # Four-word record equations for a postorder copy -/

namespace ThreeFlat.RAM.HistoryJoinScan

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing BigOperators

variable {w : ℕ}

/-- Cast only the six individual descriptor words into the arithmetic modulus. -/
def Header.words (c : Header ℕ) : Header (Word w) :=
  ⟨c.source,c.dest,c.pins,c.oldPins,c.newPins,c.offset⟩

private theorem word_lt {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    (x : Word w) < (y : Word w) ↔ x < y := by
  change ((x : Word w) : ℕ) < ((y : Word w) : ℕ) ↔ _
  rw [Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

/-- The native descriptor's value at the literal address of a row and column.
Only the taken pin branch needs a valid mapping record. -/
theorem at_record (c : Header ℕ) (m : Memory w) (i : ℕ) (j : Fin 4) (raw : ℕ)
    (mapPin : ℕ → ℕ) (wide : 4 < 2^w) (data_fit : 4*i+j.val < 2^w)
    (source_fit : c.source+(4*i+j.val) < 2^w) (raw_fit : raw < 2^w)
    (old_fit : 2+c.oldPins < 2^w) (get : m (c.source+(4*i+j.val)) = (raw : Word w))
    (map_fit : 2 ≤ raw → raw < 2+c.oldPins → c.pins+(raw-2) < 2^w)
    (mapping : 2 ≤ raw → raw < 2+c.oldPins → m (c.pins+(raw-2)) = (mapPin (raw-2) : Word w)) :
    readWord c.words m ((c.dest+(4*i+j.val) : ℕ) : Word w) =
      if j.val < 3 then (translate c.oldPins c.newPins c.offset mapPin raw : Word w) else (raw : Word w) := by
  have sub : ((c.dest+(4*i+j.val) : ℕ) : Word w) - (c.dest : Word w) = ((4*i+j.val : ℕ) : Word w) := by
    rw [Nat.cast_add]; abel
  have hc : BinaryOp.eval .mod ((4*i+j.val : ℕ) : Word w) 4 = (j.val : Word w) := by
    have four : (4 : Word w).val = 4 := Nat.mod_eq_of_lt wide
    simp only [BinaryOp.eval,Fin.val_cast_of_lt data_fit,four]
    have mod : (4*i+j.val)%4 = j.val := by omega
    rw [mod]; rfl
  have origin : ((c.source : Word w)+((4*i+j.val : ℕ) : Word w)).val = c.source+(4*i+j.val) := by
    rw [← Nat.cast_add, Fin.val_cast_of_lt source_fit]
  have cj : (j.val : Word w) < 3 ↔ j.val < 3 := word_lt (x:=j.val) (y:=3) (by have := j.isLt; omega) (by omega)
  have small : (raw : Word w) < 2 ↔ raw < 2 := word_lt (x:=raw) (y:=2) raw_fit (by omega)
  have pin : (raw : Word w) < 2+(c.oldPins : Word w) ↔ raw < 2+c.oldPins := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using word_lt raw_fit old_fit
  simp only [readWord,Header.words,sub,hc,origin,get,cj,small,pin]
  by_cases coeff : j.val < 3
  · rw [ite_eq_left coeff, ite_eq_left coeff]
    by_cases lit : raw < 2
    · simp [lit,translate]
    · simp only [lit,ite_false,translate]
      by_cases mapped : raw < 2+c.oldPins
      · simp only [mapped,ite_true]
        have h2 : 2 ≤ raw := by omega
        have off : (raw : Word w) - 2 = ((raw-2 : ℕ) : Word w) := by rw [Nat.cast_sub h2]; rfl
        rw [off, ← Nat.cast_add, Fin.val_cast_of_lt (map_fit h2 mapped), mapping h2 mapped]
      · simp only [mapped,ite_false]
        rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub (by omega : c.oldPins ≤ raw)]
  · simp [coeff]

/-- Instantiating the pointer input from a real joined network is direct: all
non-tag columns have exactly the underlying resolved trivalent addresses. -/
theorem at_source {F : Type*} {n p h : ℕ} {arity : Fin n → ℕ}
    (N : (i : Fin n) → BitNetwork F (arity i)) (wire : (i : Fin n) → Fin (arity i) → BitSource h p)
    (c : Header ℕ) (i : Fin n) (row : Fin (N i).cells) (col : Fin 3) (m : Memory w)
    (mapPin : ℕ → ℕ) (map_ok : ∀ j, mapPin j.val = BitLayout.sourceAddress
      (BitNetwork.Ordered.resolve N wire i (.pin j)))
    (hi : c.oldPins = arity i) (ho : c.newPins = p)
    (hp : c.offset = h + ∑ z : Fin i.val, (N (Fin.castLE i.isLt.le z)).internal)
    (native : readWord c.words m ((c.dest+(4*row.val+col.val) : ℕ) : Word w) =
      (translate c.oldPins c.newPins c.offset mapPin (BitLayout.sourceAddress ((N i).source row col)) : Word w)) :
    readWord c.words m ((c.dest+(4*row.val+col.val) : ℕ) : Word w) =
      (BitLayout.sourceAddress ((BitNetwork.Ordered.glue N wire).source
        (finSigmaFinEquiv ⟨i,row⟩) col) : Word w) := by
  rw [native,hi,ho,hp,translate_source N wire i mapPin map_ok,BitNetwork.Ordered.source_at]
  rfl

/-- A four-word row containing a parent pointer can use the same native
join to look up its final group. Parent groups occupy column zero of a
four-word table. Columns one through three pass through as zero. -/
theorem group_column (c : Header ℕ) {n : ℕ} (parent : Fin n) (j : Fin 4) (g : ℕ)
    (mapPin : ℕ → ℕ) (shape : c.oldPins = 4*n) (look : mapPin (4*parent.val) = g) :
    let raw := if j.val = 0 then 2 + 4*parent.val else 0
    (if j.val < 3 then translate c.oldPins c.newPins c.offset mapPin raw else raw) =
      if j.val = 0 then g else 0 := by
  dsimp only
  by_cases h : j.val = 0
  · have hj : j.val < 3 := by omega
    have hp := parent.isLt
    simp [h,translate,shape,look,show 2+4*parent.val < 2+4*n by omega]; omega
  · simp [h,translate]

end ThreeFlat.RAM.HistoryJoinScan

end OAI
