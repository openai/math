import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Fixed native addressing formulas for initial gate, comparison and padding rows -/

namespace ThreeFlat.RAM.TraceBucketFields
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

/-- Original trivalent gate operands. Data registers are the requested
field, original source address, actual owner, receiving row, cells per
row, within-row slot, low-row count, owned pins, total tags, one port
bank size, high-stage bit divisor, dictionary base and public LUT base. -/
private abbrev R := @Formula.reg 13
def delta : Formula 13 := .op .bitXor (R 2) (R 3)
def reserve : Formula 13 := add (mul (add (mul (add (mul (.load (add (R 11) delta)) (R 6))
  (rem (R 2) (R 6))) (R 4)) (R 5)) (.lit 3)) (R 0)
def original : Formula 13 := lt (R 0) (.lit 3)
  (lt (R 1) (.lit 2) (R 1)
    (add (add (add (add (.lit 2) (R 7)) (R 9)) (mul (rem (div delta (R 10)) (.lit 2)) (R 8))) reserve))
  (.load (add (R 12) (R 5)))

def originalNat (m : ℕ → ℕ) (v : Fin 13 → ℕ) : ℕ :=
  let mask := v 2 ^^^ v 3
  let address := (((m (v 11+mask)*v 6+v 2%v 6)*v 4+v 5)*3+v 0)
  if v 0<3 then if v 1<2 then v 1 else 2+v 7+v 9+((mask/v 10)%2)*v 8+address
  else m (v 12+v 5)

theorem original_nat (W : ℕ) (data : Param→ℕ) (m : ℕ→ℕ) (v : Fin 13→ℕ) :
    original.natural W data m v = originalNat m v := by
  by_cases h : v 0<3 <;> by_cases g : v 1<2 <;>
    simp [original,originalNat,delta,reserve,Formula.natural,natOp,natTest,R,h,g]

/-- Reservation comparison operands. Inputs are field, absolute source,
owner row, queried row, mask ordinal, depth, external pin count, global
lane pin start, owned pins, twice bank size,
computed hidden slot, send arc, total tags, tag ordinal and equality ID. -/
private abbrev T := @Formula.reg 15
def emit : Formula 15 :=
  lt (T 1) (.lit 2) (.lit 0) (eqz (T 4) (add (T 5) (.lit 1)) (.lit 0)
    (eqz (T 2) (T 3) (lt (T 1) (add (.lit 2) (T 6)) (sub (T 1) (T 7))
      (add (add (add (.lit 2) (T 8)) (T 9)) (T 10))) (.lit 0)))
def compare : Formula 15 := eqz (T 0) (.lit 0)
  (add (add (add (.lit 2) (T 8)) (mul (T 11) (T 12))) (T 13))
  (eqz (T 0) (.lit 1) emit (eqz (T 0) (.lit 2) (.lit 0) (T 14)))

def compareNat (v : Fin 15→ℕ) : ℕ :=
  let send := 2+v 8+v 11*v 12+v 13
  let translated := if v 1<2+v 6 then v 1-v 7 else 2+v 8+v 9+v 10
  let emitted := if v 1<2 then 0 else if v 4=v 5+1 then 0 else if v 2=v 3 then translated else 0
  if v 0=0 then send else if v 0=1 then emitted else if v 0=2 then 0 else v 14

theorem compare_nat (W : ℕ) (data : Param→ℕ) (m : ℕ→ℕ) (v : Fin 15→ℕ) :
    compare.natural W data m v = compareNat v := by
  by_cases a : v 0=0 <;> by_cases b : v 0=1 <;> by_cases c : v 0=2 <;>
    by_cases g : v 1<2 <;> by_cases h : v 4=v 5+1 <;> by_cases i : v 2=v 3 <;>
    by_cases j : v 1<2+v 6 <;>
      simp [compare,compareNat,emit,T,Formula.natural,natOp,natTest,a,b,c,g,h,i,j]

/-- The padding row reads the same hidden slot on all three legs. The last
word is the constant-unit LUT on occupied slots and the zero-test otherwise. -/
private abbrev U := @Formula.reg 7
def hole : Formula 7 := lt (U 0) (.lit 3) (add (add (add (.lit 2) (U 1)) (U 2)) (U 3))
  (eqz (U 4) (.lit 0) (U 5) (U 6))

theorem hole_nat (W : ℕ) (data : Param→ℕ) (m : ℕ→ℕ) (v : Fin 7→ℕ) :
    hole.natural W data m v = if v 0<3 then 2+v 1+v 2+v 3 else if v 4=0 then v 5 else v 6 := by
  by_cases a : v 0<3 <;> by_cases b : v 4=0 <;>
    simp [hole,U,Formula.natural,natOp,natTest,a,b]

theorem costs {W K : ℕ} (p : Param → Fin K) :
    (original.compile p : Term W K 13).binds≤100 ∧ (compare.compile p : Term W K 15).binds≤100 ∧
      (hole.compile p : Term W K 7).binds≤24 := by simp only [Formula.binds_compile]; decide

end ThreeFlat.RAM.TraceBucketFields

end OAI
