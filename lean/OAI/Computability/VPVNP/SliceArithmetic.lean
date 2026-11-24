import OAI.Computability.VPVNP.SliceField

/-!
# Binary coefficient vectors for the evaluator's slice field

The prime modulus, extension degree and low coefficients of the defining monic
polynomial come from the advice. An extension-field element is represented by
its coefficients in increasing degree order. Each coefficient occupies
`clog 2 p` bits in the evaluator's little-endian word format.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic

open Polynomial

/-- Canonical residues of the `e` low coefficients, in increasing degree order. -/
abbrev Vector (p e : ℕ) := Fin e → Fin p

/-- Encode the coefficient vector with exactly `e * clog 2 p` bits. -/
def encode {p e : ℕ} (v : Vector p e) : Fin (e * Nat.clog 2 p) → Bool :=
  RAMSerialization.arrayBits e (Nat.clog 2 p) fun i =>
    ⟨(v i).val, (v i).isLt.trans_le (Nat.le_pow_clog (by decide) p)⟩

/-- Decode all bit strings by reducing each word modulo the supplied prime. -/
def ofBits {p e : ℕ} [NeZero p] (bits : Fin (e * Nat.clog 2 p) → Bool) : Vector p e :=
  let words := (RAMSerialization.arrayBits e (Nat.clog 2 p)).symm bits
  fun i => ⟨(words i).val % p, Nat.mod_lt _ (NeZero.pos p)⟩

@[simp] theorem ofBits_encode {p e : ℕ} [NeZero p] (v : Vector p e) :
    ofBits (encode v) = v := by
  funext i
  apply Fin.ext
  simp [ofBits, encode, Nat.mod_eq_of_lt (v i).isLt]

/-- Read the advised polynomial from its low coefficients. -/
noncomputable def modulus {p e : ℕ} (c : Vector p e) : (ZMod p)[X] :=
  X ^ e + ∑ i, C ((c i).val : ZMod p) * X ^ i.val

theorem modulus_monic {p e : ℕ} (c : Vector p e) :
    (modulus c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem modulus_natDegree {p e : ℕ} [Nontrivial (ZMod p)] (c : Vector p e) :
    (modulus c).natDegree = e := by
  rw [modulus, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa using degree_sum_fin_lt (fun i : Fin e => ((c i).val : ZMod p))

theorem modulus_ofBits {p e : ℕ} [NeZero p] (bits : Fin (e * Nat.clog 2 p) → Bool) :
    modulus (ofBits bits) = SliceField.polynomialOfBits p e bits := by
  simp only [modulus, SliceField.polynomialOfBits, ofBits, ZMod.natCast_mod]

/-- Interpret a coefficient vector in the advised quotient ring. -/
noncomputable def value {p e : ℕ} (f : (ZMod p)[X]) (v : Vector p e) : AdjoinRoot f :=
  ∑ i, algebraMap (ZMod p) (AdjoinRoot f) ((v i).val : ZMod p) * AdjoinRoot.root f ^ i.val

/-- The zero element in the power basis, with zero in each of the `e` coefficient positions. -/
def zero (p e : ℕ) [NeZero p] : Vector p e := fun _ => 0

/-- Power-basis vector of the constant polynomial one, with its unit coefficient in degree
zero. -/
def one (p e : ℕ) [NeZero p] : Vector p e := fun i => if i.val = 0 then 1 else 0

/-- Add the two power-basis vectors coefficientwise modulo `p`. -/
def add {p e : ℕ} (a b : Vector p e) : Vector p e := fun i => a i + b i

/-- Multiply every coefficient of a power-basis vector by the prime-field scalar `a`. -/
def scale {p e : ℕ} (a : Fin p) (v : Vector p e) : Vector p e := fun i => a * v i

/-- The residue of a canonical limb is the image under the finite-ring equivalence. -/
theorem cast_val_eq_finEquiv {p : ℕ} [NeZero p] (a : Fin p) :
    (a.val : ZMod p) = ZMod.finEquiv p a := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => exact ZMod.natCast_zmod_val (n := p + 1) a

@[simp] theorem value_zero {p e : ℕ} [NeZero p] (f : (ZMod p)[X]) :
    value f (zero p e) = 0 := by simp [value, zero]

@[simp] theorem value_one {p e : ℕ} [NeZero p] [NeZero e] (f : (ZMod p)[X]) :
    value f (one p e) = 1 := by
  rw [value, Finset.sum_eq_single (0 : Fin e)]
  · simp [one]
  · intro i _ hi
    have : i.val ≠ 0 := by simpa using hi
    simp [one, this]
  · simp

@[simp] theorem value_add {p e : ℕ} [NeZero p] (f : (ZMod p)[X]) (a b : Vector p e) :
    value f (add a b) = value f a + value f b := by
  simp only [value, add, cast_val_eq_finEquiv, map_add, add_mul, Finset.sum_add_distrib]

@[simp] theorem value_scale {p e : ℕ} [NeZero p] (f : (ZMod p)[X]) (a : Fin p) (v : Vector p e) :
    value f (scale a v) = algebraMap (ZMod p) _ (a.val : ZMod p) * value f v := by
  simp only [value, scale, cast_val_eq_finEquiv, map_mul, Finset.mul_sum, mul_assoc]

/-- Decoding a vector and taking its `i`th power-basis coordinate recovers the
stored limb exactly. -/
theorem repr_value {p e : ℕ} {f : (ZMod p)[X]} (hm : f.Monic)
    (he : f.natDegree = e) (v : Vector p e) (i : Fin e) :
    (AdjoinRoot.powerBasis' hm).basis.repr (value f v) (i.cast he.symm) = (v i).val := by
  subst e
  let b := AdjoinRoot.powerBasisAux' hm
  have h (j : Fin f.natDegree) : b j = AdjoinRoot.root f ^ j.val :=
    (AdjoinRoot.powerBasis' hm).basis_eq_pow j
  have heq : value f v = ∑ j, ((v j).val : ZMod p) • b j := by simp [value, h, Algebra.smul_def]
  change b.repr (value f v) i = _
  rw [heq, map_sum]
  simp [Finsupp.finsetSum_apply, map_smul, Finsupp.single_apply]

theorem value_injective {p e : ℕ} [NeZero p] {f : (ZMod p)[X]} (hm : f.Monic)
    (he : f.natDegree = e) : Function.Injective (value (e := e) f) := by
  intro u v huv
  funext i
  apply (ZMod.finEquiv p).injective
  rw [← cast_val_eq_finEquiv, ← cast_val_eq_finEquiv, ← repr_value hm he u i, huv, repr_value hm he v i]

end SliceArithmetic

end VPVNP
end Computability
end OAI
