import OAI.ThreeFlat.RAM.ContractionSteps
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Reading a cell and multiplying its value in the encoded network -/

namespace ThreeFlat.RAM.Contraction

open Computability.VPVNP.BurstRAM BitLayout Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}

def cellAddr (N : BitNetwork F p) (i : ℕ) : ℕ := cellsBase p N.internal + 11 * i

/-- All public input, workspace, eleven-word cell records, and the entire
multiplication table fit in the address space. -/
def Fits (N : BitNetwork F p) (w : ℕ) : Prop :=
  mulBase p N.internal N.cells + Fintype.card F * Fintype.card F ≤ 2 ^ w

variable (N : BitNetwork F p) (fit : Fits N w)
variable (code : FieldCode F w) (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)

include fit

theorem mulBase_lt : mulBase p N.internal N.cells < 2 ^ w := by
  have h := Fintype.card_pos (α := F)
  exact (Nat.lt_add_of_pos_right (Nat.mul_pos h h)).trans_le fit

theorem card_le_word : Fintype.card F ≤ 2 ^ w := by
  exact (Nat.le_mul_of_pos_right _ Fintype.card_pos).trans
    ((Nat.le_add_left _ _).trans fit)

theorem cellAddr_lt {i : ℕ} (hi : i ≤ N.cells) : cellAddr N i < 2 ^ w :=
  (Nat.add_le_add_left (Nat.mul_le_mul_left 11 hi) _).trans_lt (mulBase_lt N fit)

theorem cell_offset_lt (i : Fin N.cells) {j : ℕ} (hj : j < 11) :
    cellAddr N i.val + j < 2 ^ w := by
  have h := cellAddr_lt N fit i.isLt
  unfold cellAddr at h ⊢
  omega

theorem sourceAddress_lt (s : BitSource N.internal p) : sourceAddress s < 2 ^ w := by
  have h := cellAddr_lt N fit (Nat.zero_le N.cells)
  simp only [cellAddr, cellsBase, hiddenBase, Nat.mul_zero, Nat.add_zero] at h
  cases s with
  | hidden i => simp only [sourceAddress, hiddenBase]; omega
  | pin i => simp only [sourceAddress]; omega
  | constant b =>
    cases b
    · change 0 < 2^w
      omega
    · change 1 < 2^w
      omega

theorem readBit_cell (i : Fin N.cells) (j : Fin 3) (tail : Memory w := fun _ => 0) :
    readBit (memoryWithTail tail N code pin hidden) ((cellAddr N i.val + j.val : ℕ) : Word w) =
      bitWord w ((N.source i j).read hidden pin) := by
  rw [readBit, Fin.val_cast_of_lt (cell_offset_lt N fit i (by omega))]
  rw [cellAddr, read_wireAddress (tail := tail)]
  change memoryWithTail tail N code pin hidden (((sourceAddress (N.source i j) : ℕ) : Word w) : ℕ) = _
  rw [Fin.val_cast_of_lt (sourceAddress_lt N fit _), read_source (tail := tail)]

theorem read_coefficient (i : Fin N.cells) (tail : Memory w := fun _ => 0) :
    coefficient (memoryWithTail tail N code pin hidden) ((cellAddr N i.val : ℕ) : Word w) =
      code.encode (N.factor pin hidden i) := by
  let v := fun j : Fin 3 => (N.source i j).read hidden pin
  have bits (j : Fin 3) := readBit_cell N fit code pin hidden i j tail
  have b₀ := bits 0
  have b₁ := bits 1
  have b₂ := bits 2
  simp only [Fin.val_zero, Nat.add_zero] at b₀
  change readBit _ ((cellAddr N i.val + 1 : ℕ) : Word w) = bitWord w (v 1) at b₁
  change readBit _ ((cellAddr N i.val + 2 : ℕ) : Word w) = bitWord w (v 2) at b₂
  rw [Nat.cast_add, Nat.cast_one] at b₁
  rw [show cellAddr N i.val + 2 = cellAddr N i.val + 1 + 1 by omega] at b₂
  push_cast at b₂
  unfold coefficient
  rw [b₀, b₁, b₂]
  change memoryWithTail tail N code pin hidden _ = code.encode (N.table i v)
  rw [← read_factor N code pin hidden i v tail]
  apply congrArg (memoryWithTail tail N code pin hidden)
  let n := cellAddr N i.val + (3 + key v)
  have hn : n < 2 ^ w := cell_offset_lt N fit i (by have := key_lt v; omega)
  change _ = n
  rw [← Fin.val_cast_of_lt hn]
  congr 1
  dsimp [n, key, bitWord, v]
  push_cast
  ring

theorem read_multiplication (x y : F) (tail : Memory w := fun _ => 0) :
    let codec : FieldCode F w := FieldCode.ofCardLe (card_le_word N fit)
    let addr : Word w := codec.encode x * (Fintype.card F : Word w) + codec.encode y +
      (mulBase p N.internal N.cells : Word w)
    memoryWithTail tail N codec pin hidden addr.val = codec.encode (x*y) := by
  let a := (Fintype.equivFin F x).val
  let b := (Fintype.equivFin F y).val
  let d := Fintype.card F
  have hlt : d * a + b < d*d := by
    calc
      d * a + b < d*a + d := Nat.add_lt_add_left (Fintype.equivFin F y).isLt _
      _ = d*(a+1) := by ring
      _ ≤ d*d := Nat.mul_le_mul_left _ (Fintype.equivFin F x).isLt
  let codec : FieldCode F w := FieldCode.ofCardLe (card_le_word N fit)
  have enc (z : F) : codec.encode z = (((Fintype.equivFin F z).val : ℕ) : Word w) :=
    (Fin.cast_val_eq_self (codec.encode z)).symm
  change memoryWithTail tail N codec pin hidden _ = codec.encode (x*y)
  rw [← read_product N codec pin hidden x y tail]
  apply congrArg (memoryWithTail tail N codec pin hidden)
  change (codec.encode x * (d : Word w) + codec.encode y + _).val = _
  rw [enc, enc, ← Fin.val_cast_of_lt (show mulBase p N.internal N.cells + d*a+b < 2^w by
    exact (by omega : mulBase p N.internal N.cells + d*a + b <
      mulBase p N.internal N.cells + d*d).trans_le fit)]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul]
  dsimp [a, b]
  ring

end ThreeFlat.RAM.Contraction

end OAI
