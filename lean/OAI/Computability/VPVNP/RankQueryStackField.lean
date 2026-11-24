import OAI.Computability.VPVNP.RankQueryStackScan
import OAI.Computability.VPVNP.SliceArithmeticPower
import OAI.Computability.VPVNP.SliceArithmeticWork

/-!
# Native coefficients for the determinant stack

Each scalar in a continuation is one canonical base-`p` word with `e` digits.
The product unpacks both words, uses Horner multiplication modulo the advised
monic polynomial, and packs the reduced answer. The interpretation in the
advised quotient is an injective ring homomorphism.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

open SliceArithmetic

/-- Numeric scalar representation with a fixed advised modulus. -/
structure Scalar {p e : ℕ} (c : Vector p e) where
  /-- Packed index of the scalar's `e` base-`p` coordinates. -/
  code : Fin (p^e)
  deriving DecidableEq

namespace Scalar

variable {p e : ℕ} {c : Vector p e}

/-- Pack a vector of prime-field coordinates into its finite scalar code. -/
def pack (c : Vector p e) (v : Vector p e) : Scalar c := ⟨finFunctionFinEquiv v⟩

/-- Decode the scalar's packed index into its vector of prime-field coordinates. -/
def digits (s : Scalar c) : Vector p e := finFunctionFinEquiv.symm s.code

@[simp] theorem digits_pack (v : Vector p e) : (pack c v).digits = v := finFunctionFinEquiv.symm_apply_apply v

@[simp] theorem pack_digits (s : Scalar c) : pack c s.digits = s := by
  cases s; simp [pack, digits]

/-- Evaluate the decoded coordinate polynomial at the adjoined root of the modulus. -/
noncomputable def interpret (s : Scalar c) : AdjoinRoot (modulus c) :=
  SliceArithmetic.value (modulus c) s.digits

variable [Fact p.Prime] [NeZero e]

omit [NeZero e] in
theorem interpret_injective (c : Vector p e) : Function.Injective (interpret (c := c)) := by
  intro a b hab
  have hd := value_injective (modulus_monic c) (modulus_natDegree c) hab
  simpa only [pack_digits] using congrArg (pack c) hd

instance : Zero (Scalar c) := ⟨pack c (SliceArithmetic.zero p e)⟩
instance : One (Scalar c) := ⟨pack c (SliceArithmetic.one p e)⟩
instance : Add (Scalar c) := ⟨fun a b => pack c (SliceArithmetic.add a.digits b.digits)⟩
/-- Materialize each round of the extension-field product before the next round. -/
def product (a b : Scalar c) : Scalar c :=
  let result := Stream.product (List.ofFn c) (List.ofFn a.digits) (List.ofFn b.digits)
  pack c fun i => result.coefficients[i.val]?.getD 0

instance : Mul (Scalar c) := ⟨product⟩

omit [NeZero e] in
theorem product_eq (a b : Scalar c) : a*b = pack c (SliceArithmetic.mul c a.digits b.digits) := by
  change product a b = _
  unfold product
  rw [Stream.product_correct]
  apply congrArg (pack c)
  funext i
  simp [i.isLt]
instance : Neg (Scalar c) := ⟨fun a => pack c (scale (-1) a.digits)⟩
instance : Sub (Scalar c) := ⟨fun a b => a + -b⟩
instance : SMul ℕ (Scalar c) := ⟨fun n a => pack c (scale ((ZMod.finEquiv p).symm n) a.digits)⟩
instance : SMul ℤ (Scalar c) := ⟨fun n a => pack c (scale ((ZMod.finEquiv p).symm n) a.digits)⟩
instance : Pow (Scalar c) ℕ := ⟨fun a n => pack c (SliceArithmetic.pow c a.digits n)⟩
instance : NatCast (Scalar c) := ⟨fun n => n • (1 : Scalar c)⟩
instance : IntCast (Scalar c) := ⟨fun n => n • (1 : Scalar c)⟩

omit [NeZero e] in
private theorem map_zero : interpret (0 : Scalar c) = 0 := by
  change value (modulus c) (pack c (SliceArithmetic.zero p e)).digits = _
  simp

private theorem map_one : interpret (1 : Scalar c) = 1 := by
  change value (modulus c) (pack c (SliceArithmetic.one p e)).digits = _
  simp

omit [NeZero e] in
private theorem map_add (a b : Scalar c) : interpret (a+b) = interpret a + interpret b := by
  change value (modulus c) (pack c (SliceArithmetic.add a.digits b.digits)).digits = _
  rw [digits_pack, value_add]; rfl

omit [NeZero e] in
private theorem map_mul (a b : Scalar c) : interpret (a*b) = interpret a * interpret b := by
  rw [product_eq]
  change value (modulus c) (pack c (SliceArithmetic.mul c a.digits b.digits)).digits = _
  rw [digits_pack, value_mul]; rfl

omit [NeZero e] in
private theorem map_neg (a : Scalar c) : interpret (-a) = -interpret a := by
  change value (modulus c) (pack c (scale (-1) a.digits)).digits = _
  simp [cast_val_eq_finEquiv, interpret]

omit [NeZero e] in
private theorem map_nsmul (n : ℕ) (a : Scalar c) : interpret (n • a) = n • interpret a := by
  change value (modulus c) (pack c (scale ((ZMod.finEquiv p).symm n) a.digits)).digits = _
  simp [cast_val_eq_finEquiv, interpret, nsmul_eq_mul]

omit [NeZero e] in
private theorem map_zsmul (n : ℤ) (a : Scalar c) : interpret (n • a) = n • interpret a := by
  change value (modulus c) (pack c (scale ((ZMod.finEquiv p).symm n) a.digits)).digits = _
  simp [cast_val_eq_finEquiv, interpret, zsmul_eq_mul]

private theorem map_pow (a : Scalar c) (n : ℕ) : interpret (a^n) = (interpret a)^n := by
  change value (modulus c) (pack c (SliceArithmetic.pow c a.digits n)).digits = _
  rw [digits_pack, value_pow]; rfl

instance : CommRing (Scalar c) := fast_instance%
  (interpret_injective c).commRing _ map_zero map_one map_add map_mul map_neg
    (fun x y => by change interpret (x + -y) = _; rw [map_add, map_neg, sub_eq_add_neg])
    map_nsmul map_zsmul map_pow
    (fun n => by change interpret (n • (1 : Scalar c)) = _; rw [map_nsmul, map_one, nsmul_eq_mul, mul_one])
    (fun n => by change interpret (n • (1 : Scalar c)) = _; rw [map_zsmul, map_one, zsmul_eq_mul, mul_one])

/-- Ring homomorphism interpreting encoded scalars in the algebra obtained by adjoining a root
of the modulus. -/
noncomputable def interpretation (c : Vector p e) : Scalar c →+* AdjoinRoot (modulus c) where
  toFun := interpret
  map_zero' := map_zero
  map_one' := map_one
  map_add' := map_add
  map_mul' := map_mul

omit [Fact p.Prime] [NeZero e] in
/-- Every scalar occupies at most `e * clog 2 p` bits. -/
theorem code_lt (a : Scalar c) : a.code.val < 2 ^ (e * Nat.clog 2 p) := calc
  _ < p^e := a.code.isLt
  _ ≤ (2^Nat.clog 2 p)^e := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
  _ = _ := by rw [← pow_mul, Nat.mul_comm]

end Scalar

end RankQuery.Stack

end VPVNP
end Computability
end OAI
