import Init.Data.BitVec.Bitblast
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.NormNum

/-! A signed fixed-width ripple-carry circuit for comparing and adding integer prices.
The counters measure Boolean gates. The circuit visits one pair of input bits per stage. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Binary

/-- The carry and sum share one XOR, giving a five-gate cell. -/
def cell (x y c : Bool) : Bool × Bool :=
  let t := x ^^ y
  ((x && y) || (t && c), t ^^ c)

theorem cell_spec (x y c : Bool) : cell x y c = BitVec.adcb x y c := by
  cases x <;> cases y <;> cases c <;> decide

def addCarry {width : ℕ} (x y : BitVec width) (initial : Bool) :
    (Bool × ℕ) × BitVec width :=
  BitVec.iunfoldr (fun (i : Fin width) (s : Bool × ℕ) =>
    let z := cell (x.getLsbD i) (y.getLsbD i) s.1
    ((z.1, s.2 + 5), z.2)) (initial, 0)

theorem addCarry_spec {width : ℕ} (x y : BitVec width) (initial : Bool) :
    addCarry x y initial = ((BitVec.carry width x y initial, 5*width),
      x+y+BitVec.setWidth width (BitVec.ofBool initial)) := by
  unfold addCarry
  apply BitVec.iunfoldr_replace (fun j => (BitVec.carry j x y initial, 5*j))
    (x+y+BitVec.setWidth width (BitVec.ofBool initial)) (initial,0)
  · simp
  · intro j
    simp [cell_spec, BitVec.adcb, BitVec.carry_succ, BitVec.getElem_add_add_bool, Nat.mul_add]

/-- Fixed-width addition computes the sum by a deterministic pass through the bits. -/
def add {width : ℕ} (x y : BitVec width) : BitVec width × ℕ :=
  let z := addCarry x y false
  (z.2, z.1.2)

theorem add_spec {width : ℕ} (x y : BitVec width) :
    add x y = (x+y, 5*width) := by simp [add, addCarry_spec]

/-- The carry of the bitwise subtraction determines order after correcting for sign.
Inverting the second bit, one XOR, two ANDs and one OR are the five gates per cell. -/
def compareCarry {width : ℕ} (x y : BitVec width) : Bool × ℕ :=
  (BitVec.iunfoldr (fun (i : Fin width) (s : Bool × ℕ) =>
    let a := x.getLsbD i
    let b := !y.getLsbD i
    (((a && b) || ((a ^^ b) && s.1), s.2+5), false)) (true,0)).1

theorem compareCarry_spec {width : ℕ} (x y : BitVec width) :
    compareCarry x y = (BitVec.carry width x (~~~y) true, 5*width) := by
  unfold compareCarry
  apply BitVec.iunfoldr.fst_eq (fun j => (BitVec.carry j x (~~~y) true, 5*j)) (true,0)
  · simp
  · intro j
    simp [BitVec.carry_succ, j.isLt, Nat.mul_add]
    cases x[j.val] <;> cases y[j.val] <;> cases BitVec.carry j.val x (~~~y) true <;> decide

def signedLT {width : ℕ} (x y : BitVec width) : Bool × ℕ :=
  let c := compareCarry x y
  ((x.msb == y.msb) ^^ c.1, c.2+2)

theorem signedLT_spec {width : ℕ} (x y : BitVec width) :
    signedLT x y = (decide (x.toInt < y.toInt), 5*width+2) := by
  rw [signedLT, compareCarry_spec, ← BitVec.slt_eq_decide, BitVec.slt_eq_not_carry]

/-- A sign bit in addition to the magnitude bound suffices for every score in the run. -/
def widthFor (B : ℕ) := B.size+1

theorem decode_word {B : ℕ} {z : ℤ} (hz : |z| ≤ (B : ℤ)) :
    (BitVec.ofInt (widthFor B) z).toInt = z := by
  have hb : (B : ℤ) < 2^B.size := by exact_mod_cast Nat.lt_size_self B
  obtain ⟨hl, hr⟩ := abs_le.mp hz
  apply BitVec.toInt_ofInt_eq_self
  · simp [widthFor]
  · simp only [widthFor, Nat.add_sub_cancel]
    omega
  · simp only [widthFor, Nat.add_sub_cancel]
    omega

theorem add_word {width : ℕ} (x y : ℤ) :
    add (BitVec.ofInt width x) (BitVec.ofInt width y) = (BitVec.ofInt width (x+y), 5*width) := by
  rw [add_spec, BitVec.ofInt_add]

theorem compare_word {B : ℕ} {x y : ℤ} (hx : |x| ≤ (B : ℤ)) (hy : |y| ≤ (B : ℤ)) :
    signedLT (BitVec.ofInt (widthFor B) x) (BitVec.ofInt (widthFor B) y) =
      (decide (x<y), 5*widthFor B+2) := by rw [signedLT_spec, decode_word hx, decode_word hy]

end Binary
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
