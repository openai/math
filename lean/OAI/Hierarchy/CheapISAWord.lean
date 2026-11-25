import OAI.Computability.VPVNP.RAMProgram
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # A five-bit extension of the native word preserves masked arithmetic -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

def width (w : ℕ) := w+5

def wide {w : ℕ} (x : Word w) : Word (width w) := (x.val:Word (width w))

def mask (w : ℕ) : Word (width w) := ((2^w-1:ℕ):Word (width w))

private theorem capacity (w : ℕ) : 2^width w=2^w*32 := by simp [width,Nat.pow_add]

private theorem divides (w : ℕ) : 2^w ∣ 2^width w := ⟨32,capacity w⟩

private theorem room (w : ℕ) : 2^w≤2^width w := by rw [capacity];omega

@[simp] theorem wide_val {w : ℕ} (x : Word w) : (wide x).val=x.val :=
  Fin.val_cast_of_lt (Nat.lt_of_lt_of_le x.isLt (room w))

theorem wide_injective {w : ℕ} : Function.Injective (@wide w) := by
  intro x y eqn
  exact Fin.ext (by simpa only [wide_val] using congrArg Fin.val eqn)

@[simp] theorem wide_lt_iff {w : ℕ} (x y : Word w) : wide x<wide y ↔ x<y := by
  change (wide x).val<(wide y).val ↔ x.val<y.val
  simp only [wide_val]

@[simp] theorem wide_zero (w : ℕ) : wide (0:Word w)=0 := by
  apply Fin.ext
  simp only [wide_val,Fin.val_zero]

@[simp] theorem mask_val (w : ℕ) : (mask w).val=2^w-1 := by
  have pos : 0<2^w := Nat.two_pow_pos w
  exact Fin.val_cast_of_lt (Nat.lt_of_lt_of_le (show 2^w-1<2^w by omega) (room w))

private theorem and_val {w : ℕ} (a b : Word w) :
    (BinaryOp.bitAnd.eval a b).val=(a.val &&& b.val) := by
  change (a.val &&& b.val)%(2^w)=(a.val &&& b.val)
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)

theorem mask_read {w : ℕ} (x : Word (width w)) :
    (BinaryOp.bitAnd.eval x (mask w)).val=x.val%(2^w) := by
  rw [and_val,mask_val,Nat.and_two_pow_sub_one_eq_mod]

theorem wide_add {w : ℕ} (x y : Word w) :
    BinaryOp.bitAnd.eval (wide x+wide y) (mask w)=wide (x+y) := by
  apply Fin.ext
  simp only [mask_read,wide_val,Fin.val_add]
  exact Nat.mod_mod_of_dvd _ (divides w)

theorem wide_sub {w : ℕ} (x y : Word w) :
    BinaryOp.bitAnd.eval (wide x-wide y) (mask w)=wide (x-y) := by
  apply Fin.ext
  simp only [mask_read,wide_val,Fin.val_sub]
  rw [Nat.mod_mod_of_dvd _ (divides w)]
  have shift : 2^width w-y.val+x.val=(2^w-y.val+x.val)+2^w*31 := by
    rw [capacity]
    have bound:=y.isLt
    omega
  rw [shift,Nat.add_mul_mod_self_left]

theorem wide_bitAnd {w : ℕ} (x y : Word w) :
    BinaryOp.bitAnd.eval (wide x) (wide y)=wide (BinaryOp.bitAnd.eval x y) := by
  apply Fin.ext
  simp only [and_val,wide_val]

end Hierarchy.CheapISA

end OAI
