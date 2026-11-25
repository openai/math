import OAI.Computability.NearSquareRoot.ScheduleGeneratorBounds

/-! # Primitive recursive dyadic arithmetic for template validation

A signed numerator is the difference of two naturals. Keeping both parts
makes multiplication and sign change primitive recursive on product codes.
The last natural is the exponent of the power-of-two denominator. Equality
compares cross products and therefore permits unreduced representations. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableDyadic

abbrev Code := (ℕ × ℕ) × ℕ

def value (x : Code) : ℚ := ((x.1.1 : ℚ) - x.1.2) / 2^x.2

def zero : Code := ((0,0),0)
def one : Code := ((1,0),0)
def negOne : Code := ((0,1),0)
def half : Code := ((1,0),1)
def negHalf : Code := ((0,1),1)

def neg (x : Code) : Code := ((x.1.2, x.1.1), x.2)

def add (x y : Code) : Code :=
  ((x.1.1 * 2^y.2 + y.1.1 * 2^x.2, x.1.2 * 2^y.2 + y.1.2 * 2^x.2), x.2 + y.2)

def mul (x y : Code) : Code :=
  ((x.1.1 * y.1.1 + x.1.2 * y.1.2, x.1.1 * y.1.2 + x.1.2 * y.1.1), x.2 + y.2)

def equal (x y : Code) : Bool :=
  decide (x.1.1 * 2^y.2 + y.1.2 * 2^x.2 = y.1.1 * 2^x.2 + x.1.2 * 2^y.2)

/-- Decode the natural-number encoding used by `Encodable ℤ` and attach
the supplied denominator exponent. Even numerators encode nonnegative integers. -/
def fromSigned (n e : ℕ) : Code :=
  if n % 2 = 0 then ((n/2,0),e) else ((0,n/2+1),e)

def sum (xs : List Code) : Code := xs.foldr add zero
def prod (xs : List Code) : Code := xs.foldr mul one

private theorem pos {α : Type*} [Primcodable α] {f : α → Code} (hf : Primrec f) :
    Primrec fun t => (f t).1.1 := Primrec.fst.comp (Primrec.fst.comp hf)

private theorem minus {α : Type*} [Primcodable α] {f : α → Code} (hf : Primrec f) :
    Primrec fun t => (f t).1.2 := Primrec.snd.comp (Primrec.fst.comp hf)

private theorem exponent {α : Type*} [Primcodable α] {f : α → Code} (hf : Primrec f) :
    Primrec fun t => (f t).2 := Primrec.snd.comp hf

private theorem denom {α : Type*} [Primcodable α] {f : α → Code} (hf : Primrec f) :
    Primrec fun t => 2^(f t).2 := Generator.primrecNatPow.comp (.const 2) (exponent hf)

theorem primrec_neg : Primrec neg :=
  ((minus .id).pair (pos .id)).pair (exponent .id)

theorem primrec_add : Primrec₂ add :=
  ((Primrec.nat_add.comp (Primrec.nat_mul.comp (pos .fst) (denom .snd))
    (Primrec.nat_mul.comp (pos .snd) (denom .fst))).pair
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (minus .fst) (denom .snd))
    (Primrec.nat_mul.comp (minus .snd) (denom .fst)))).pair
    (Primrec.nat_add.comp (exponent .fst) (exponent .snd))

theorem primrec_mul : Primrec₂ mul :=
  ((Primrec.nat_add.comp (Primrec.nat_mul.comp (pos .fst) (pos .snd))
    (Primrec.nat_mul.comp (minus .fst) (minus .snd))).pair
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (pos .fst) (minus .snd))
    (Primrec.nat_mul.comp (minus .fst) (pos .snd)))).pair
    (Primrec.nat_add.comp (exponent .fst) (exponent .snd))

theorem primrec_equal : Primrec₂ equal :=
  Primrec.eq.decide.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (pos .fst) (denom .snd))
      (Primrec.nat_mul.comp (minus .snd) (denom .fst)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (pos .snd) (denom .fst))
      (Primrec.nat_mul.comp (minus .fst) (denom .snd)))

theorem primrec_fromSigned : Primrec₂ fromSigned :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp .fst (.const 2)) (.const 0))
    (((Primrec.nat_div.comp .fst (.const 2)).pair (.const 0)).pair .snd)
    (((Primrec.const 0).pair (Primrec.nat_add.comp (Primrec.nat_div.comp .fst (.const 2)) (.const 1))).pair .snd)

theorem primrec_sum : Primrec sum :=
  Primrec.list_foldr .id (.const zero) (primrec_add.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂

theorem primrec_prod : Primrec prod :=
  Primrec.list_foldr .id (.const one) (primrec_mul.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂

theorem computable_neg : Computable neg := primrec_neg.to_comp
theorem computable_add : Computable₂ add := primrec_add.to_comp
theorem computable_mul : Computable₂ mul := primrec_mul.to_comp
theorem computable_equal : Computable₂ equal := primrec_equal.to_comp
theorem computable_fromSigned : Computable₂ fromSigned := primrec_fromSigned.to_comp
theorem computable_sum : Computable sum := primrec_sum.to_comp
theorem computable_prod : Computable prod := primrec_prod.to_comp

@[simp] theorem value_zero : value zero = 0 := by norm_num [value, zero]
@[simp] theorem value_one : value one = 1 := by norm_num [value, one]
@[simp] theorem value_negOne : value negOne = -1 := by norm_num [value, negOne]
@[simp] theorem value_half : value half = 1/2 := by norm_num [value, half]
@[simp] theorem value_negHalf : value negHalf = -(1/2) := by norm_num [value, negHalf]

@[simp] theorem value_neg (x : Code) : value (neg x) = -value x := by unfold neg value; dsimp; ring

@[simp] theorem value_add (x y : Code) : value (add x y) = value x + value y := by
  simp only [add, value, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp
  ring

@[simp] theorem value_mul (x y : Code) : value (mul x y) = value x * value y := by
  simp only [mul, value, Nat.cast_add, Nat.cast_mul, pow_add, div_mul_div_comm]
  ring

theorem equal_iff (x y : Code) : equal x y = true ↔ value x = value y := by
  simp only [equal, decide_eq_true_eq, value, div_eq_div_iff (by positivity : (2:ℚ)^x.2 ≠ 0)
    (by positivity : (2:ℚ)^y.2 ≠ 0)]
  have he : ((x.1.1 * 2^y.2 + y.1.2 * 2^x.2 : ℕ) : ℚ) = y.1.1 * 2^x.2 + x.1.2 * 2^y.2 ↔
      x.1.1 * 2^y.2 + y.1.2 * 2^x.2 = y.1.1 * 2^x.2 + x.1.2 * 2^y.2 := by norm_cast
  rw [← he]
  push_cast
  constructor <;> intro h <;> linarith only [h]

@[simp] theorem value_fromSigned (n : ℤ) (e : ℕ) :
    value (fromSigned (Encodable.encode n) e) = n / (2:ℚ)^e := by
  cases n with
  | ofNat n =>
    change value (fromSigned (2*n) e) = _
    simp [fromSigned, value]
  | negSucc n =>
    change value (fromSigned (2*n+1) e) = _
    simp [fromSigned, value, Nat.add_div]

@[simp] theorem value_sum (xs : List Code) : value (sum xs) = (xs.map value).sum := by
  induction xs with
  | nil => exact value_zero
  | cons x xs ih => exact (value_add x (sum xs)).trans (congrArg (value x + ·) ih)

@[simp] theorem value_prod (xs : List Code) : value (prod xs) = (xs.map value).prod := by
  induction xs with
  | nil => exact value_one
  | cons x xs ih => exact (value_mul x (prod xs)).trans (congrArg (value x * ·) ih)

end KernelComputableDyadic

end NearSquareRoot
end Computability
end OAI
