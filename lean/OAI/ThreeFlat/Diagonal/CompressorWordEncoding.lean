import OAI.ThreeFlat.Diagonal.LaneCursorRows
import OAI.Computability.VPVNP.BitSlotIndex
import OAI.Computability.VPVNP.RAMProgram

namespace OAI
/-! # Computing binary tag sums by a single RAM XOR instruction -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression LaneCursor

def tagOrdinal (t : ℕ) : BitWord t ≃ Fin (2^t) := finFunctionFinEquiv

theorem decodeOrdinal (t : ℕ) (x : Fin (2^t)) :
    (tagOrdinal t).symm x = highBits t 0 x.val := by
  funext i
  apply Fin.ext
  change x.val / 2^i.val % 2 = (if (x.val >>> 0).testBit i.val then (1 : Fin 2) else 0).val
  rw [Nat.shiftRight_zero,Nat.testBit_eq_decide_div_mod_eq]
  by_cases one : x.val / 2^i.val % 2 = 1
  · simp [one]
  · have zero : x.val / 2^i.val % 2 = 0 := by omega
    simp [zero]

theorem tagOrdinal_add {t : ℕ} (a b : BitWord t) :
    (tagOrdinal t (a+b)).val = (tagOrdinal t a).val ^^^ (tagOrdinal t b).val := by
  let u := tagOrdinal t a
  let v := tagOrdinal t b
  let x : Fin (2^t) := ⟨u.val ^^^ v.val,Nat.xor_lt_two_pow u.isLt v.isLt⟩
  have hx : (tagOrdinal t).symm x = a+b := by
    rw [decodeOrdinal,show x.val = u.val ^^^ v.val from rfl,highBits_xor,
      ← decodeOrdinal t u,← decodeOrdinal t v]
    simp only [u,v,Equiv.symm_apply_apply]
    funext i
    exact (by decide : ∀ x y : Fin 2, x+y = (show ZMod 2 from x)+(show ZMod 2 from y)) (a i) (b i)
  have he : tagOrdinal t (a+b) = x := (tagOrdinal t).eq_symm_apply.mp hx.symm
  exact congrArg Fin.val he

def tagWord {t w : ℕ} (fit : t ≤ w) (a : BitWord t) : Word w :=
  (tagOrdinal t a).castLE (Nat.pow_le_pow_right (by decide) fit)

theorem tagWord_add {t w : ℕ} (fit : t ≤ w) (a b : BitWord t) :
    tagWord fit (a+b) = BinaryOp.bitXor.eval (tagWord fit a) (tagWord fit b) := by
  apply Fin.ext
  simp only [tagWord,Fin.val_castLE,BinaryOp.eval,Fin.val_ofNat,tagOrdinal_add]
  symm
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (tagWord fit a).isLt (tagWord fit b).isLt)

theorem tagWord_zero {t w : ℕ} (fit : t ≤ w) : tagWord fit (0 : BitWord t) = 0 := by
  have h := tagOrdinal_add (0 : BitWord t) 0
  simp only [add_zero,Nat.xor_self] at h
  exact Fin.ext h

theorem tagWord_sub {t w : ℕ} (fit : t ≤ w) (a b : BitWord t) :
    tagWord fit (a-b) = BinaryOp.bitXor.eval (tagWord fit a) (tagWord fit b) := by
  have neg : -b = b := by
    funext i
    exact (by decide : ∀ x : Fin 2, -x = x) (b i)
  rw [sub_eq_add_neg,neg,tagWord_add]

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
