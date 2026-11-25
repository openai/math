import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicExtension
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Data.Dyadic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Nat.Find

/-! # Executable coefficient vectors for the binary repair algebra

For `d = 2^a`, the coefficients of a reduced polynomial modulo `X^d + 1`
form a vector of `d` signed dyadics. Multiplication wraps high exponents
back into the vector and changes their sign. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CyclotomicCode

/-- Use the core implementation on signed dyadic numbers for all ring operations. -/
scoped instance : CommRing Dyadic :=
  Function.Injective.commRing Dyadic.toRat (fun _ _ h => Dyadic.toRat_inj.mp h)
    (by rfl) (by rfl) Dyadic.toRat_add Dyadic.toRat_mul Dyadic.toRat_neg Dyadic.toRat_sub
    (by intro n x; change (n * x).toRat = _; simp)
    (by intro n x; change (n * x).toRat = _; simp)
    (by simp) (by simp) (by simp)

scoped instance : Nontrivial Dyadic := ⟨⟨0, 1, by decide⟩⟩

/-- Encode a normalized dyadic by its odd signed significand and signed precision. -/
scoped instance : Encodable Dyadic :=
  Encodable.ofLeftInjection
    (fun x => match x with
      | .zero => (0, 0)
      | .ofOdd n k _ => (n, k))
    (fun (nk : ℤ × ℤ) => some (Dyadic.ofIntWithPrec nk.1 nk.2)) (by
      intro x
      cases x with
      | zero => rfl
      | ofOdd n k hn => simp [Dyadic.ofOdd_eq_ofIntWithPrec])

/-- The abstract extension used by the Hermite proof. -/
abbrev Extension (a : ℕ) := OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicExtension (-1 : Dyadic) 2 a

/-- Signed coefficients indexed by the powers strictly below the modulus degree. -/
abbrev Coeffs (a : ℕ) := Fin (2 ^ a) → Dyadic

noncomputable abbrev root (a : ℕ) : Extension a := OAI.LinearAlgebra.FiniteFourier.primeCyclotomicRoot (-1 : Dyadic) 2 a

private theorem root_pow (a : ℕ) : (root a) ^ (2 ^ a) = -1 := by
  simpa only [map_neg, map_one] using OAI.LinearAlgebra.FiniteFourier.primeCyclotomicRoot_pow (p := 2) (-1 : Dyadic) a

private noncomputable abbrev basis (a : ℕ) := OAI.LinearAlgebra.FiniteFourier.primeCyclotomicBasis (-1 : Dyadic) (p := 2) a

private theorem basis_eq (a : ℕ) (i : Fin (2^a)) : basis a i = root a ^ i.val := by
  simp only [basis, OAI.LinearAlgebra.FiniteFourier.primeCyclotomicBasis, Module.Basis.reindex_apply,
    PowerBasis.basis_eq_pow]
  rfl

/-- Interpretation is bijective. In particular equality of abstract cyclotomic
coefficients can be decided by comparing the dyadic vectors. -/
noncomputable def eval (a : ℕ) : Coeffs a ≃ₗ[Dyadic] Extension a := (basis a).equivFun.symm

theorem eval_sum (a : ℕ) (x : Coeffs a) :
    eval a x = ∑ i, algebraMap Dyadic (Extension a) (x i) * root a ^ i.val := by
  simp only [eval, Module.Basis.equivFun_symm_apply, basis_eq, Algebra.smul_def]

/-- Negacyclic convolution of two signed dyadic coefficient vectors. -/
def times (a : ℕ) (x y : Coeffs a) (k : Fin (2 ^ a)) : Dyadic :=
  ∑ i, ∑ j, if (i.val + j.val) % (2 ^ a) = k.val then
    (if i.val + j.val < 2 ^ a then x i * y j else -(x i * y j)) else 0

private theorem root_add (a : ℕ) (i j : Fin (2^a)) :
    root a ^ (i.val + j.val) =
      (if i.val + j.val < 2^a then 1 else -1) * root a ^ ((i.val + j.val) % 2^a) := by
  split_ifs with h
  · simp [Nat.mod_eq_of_lt h]
  · have h₂ := i.isLt
    have h₃ := j.isLt
    have hle : 2^a ≤ i.val + j.val := by omega
    have hlt : i.val + j.val - 2^a < 2^a := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt]
    calc
      root a ^ (i.val + j.val) =
        root a ^ (2^a + (i.val + j.val - 2^a)) := by rw [Nat.add_sub_cancel' hle]
      _ = _ := by rw [pow_add, root_pow]

theorem eval_times (a : ℕ) (x y : Coeffs a) :
    eval a (times a x y) = eval a x * eval a y := by
  rw [eval_sum, eval_sum, eval_sum]
  simp only [times, map_sum, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ j, ∑ k : Fin (2 ^ a),
          algebraMap Dyadic (Extension a)
            (if (i.val+j.val) % (2^a) = k.val then
               (if i.val+j.val < 2^a then x i*y j else -(x i*y j)) else 0) *
            root a ^ k.val := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      let k₀ : Fin (2^a) := ⟨(i.val + j.val) % (2^a), Nat.mod_lt _ (by positivity)⟩
      rw [Finset.sum_eq_single k₀]
      · simp only [k₀, ↓reduceIte]
        rw [show algebraMap Dyadic (Extension a) (x i) * root a ^ i.val *
              (algebraMap Dyadic (Extension a) (y j) * root a ^ j.val) =
              algebraMap Dyadic (Extension a) (x i * y j) * root a ^ (i.val + j.val) by
          rw [map_mul, pow_add]; ring, root_add]
        split_ifs <;> simp
      · intro k _ hne
        have : (i.val+j.val) % 2^a ≠ k.val := fun h => hne (Fin.ext h.symm)
        simp [this]
      · simp

/-- Concrete coefficient ring. Its multiplication is the signed wraparound
convolution above, while addition and subtraction act coordinatewise. -/
@[ext] structure Number (a : ℕ) where
  coeffs : Coeffs a
deriving DecidableEq

namespace Number

variable {a : ℕ}

instance : Encodable (Number a) :=
  Encodable.ofEquiv (Coeffs a) ⟨Number.coeffs, Number.mk, fun _ => rfl, fun _ => rfl⟩

/-- Include a dyadic constant in the degree-zero coefficient. -/
def ofBase (a : ℕ) (r : Dyadic) : Number a :=
  ⟨fun i => if i.val = 0 then r else 0⟩

/-- The vector and abstract extension have the same coefficients. -/
noncomputable def value (x : Number a) : Extension a := eval a x.coeffs

theorem value_injective : Function.Injective (value (a := a)) := by
  intro x y h
  exact Number.ext ((eval a).injective h)

theorem value_ofBase (r : Dyadic) : value (ofBase a r) = algebraMap Dyadic (Extension a) r := by
  rw [value, eval_sum]
  let i₀ : Fin (2 ^ a) := ⟨0, by positivity⟩
  rw [Finset.sum_eq_single i₀]
  · simp [ofBase, i₀]
  · intro k _ hk
    have h : k.val ≠ 0 := fun h => hk (Fin.ext h)
    dsimp only [ofBase]
    simp only [h, ↓reduceIte, map_zero, zero_mul]
  · simp

instance : Zero (Number a) := ⟨⟨0⟩⟩
instance : One (Number a) := ⟨ofBase a 1⟩
instance : Add (Number a) := ⟨fun x y => ⟨x.coeffs + y.coeffs⟩⟩
instance : Mul (Number a) := ⟨fun x y => ⟨times a x.coeffs y.coeffs⟩⟩
instance : Sub (Number a) := ⟨fun x y => ⟨x.coeffs - y.coeffs⟩⟩
instance : Neg (Number a) := ⟨fun x => ⟨- x.coeffs⟩⟩
instance : SMul ℕ (Number a) := ⟨fun n x => ⟨n • x.coeffs⟩⟩
instance : SMul ℤ (Number a) := ⟨fun n x => ⟨n • x.coeffs⟩⟩
instance : Pow (Number a) ℕ := ⟨fun x n => npowRec n x⟩
instance : NatCast (Number a) := ⟨fun n => ofBase a n⟩
instance : IntCast (Number a) := ⟨fun n => ofBase a n⟩

private theorem value_one : value (1 : Number a) = 1 := (value_ofBase 1).trans (map_one _)
private theorem value_mul (x y : Number a) : value (x*y) = value x * value y :=
  eval_times a x.coeffs y.coeffs

instance : CommRing (Number a) :=
  fast_instance% Function.Injective.commRing value value_injective
    ((eval a).map_zero) value_one
    (fun x y => (eval a).map_add x.coeffs y.coeffs) value_mul
    (fun x => (eval a).map_neg x.coeffs) (fun x y => (eval a).map_sub x.coeffs y.coeffs)
    (fun n x => map_nsmul (eval a) n x.coeffs) (fun n x => map_zsmul (eval a) n x.coeffs)
    (by
      intro x n
      induction n with
      | zero => exact value_one.trans (pow_zero _).symm
      | succ n ih =>
        change value (x^n * x) = _
        rw [value_mul, ih, pow_succ])
    (fun n => (value_ofBase (n : Dyadic)).trans (map_natCast _ n))
    (fun n => (value_ofBase (n : Dyadic)).trans (map_intCast _ n))

/-- Coefficient vectors form a computable presentation of the entire
localized cyclotomic algebra. -/
noncomputable def ringEquiv (a : ℕ) : Number a ≃+* Extension a where
  toFun := value
  invFun r := ⟨(eval a).symm r⟩
  left_inv x := Number.ext ((eval a).symm_apply_apply x.coeffs)
  right_inv r := (eval a).apply_symm_apply r
  map_mul' := value_mul
  map_add' x y := (eval a).map_add x.coeffs y.coeffs

instance : Nontrivial (Number a) := by
  let := OAI.LinearAlgebra.FiniteFourier.primeCyclotomicExtension_nontrivial (p := 2) (-1 : Dyadic) a
  exact (ringEquiv a).symm.injective.nontrivial

/-- The indeterminate is the second basis vector, except in the degree-one
extension where it equals `-1`. -/
def generator (a : ℕ) : Number a :=
  if 1 < 2^a then ⟨fun i => if i.val = 1 then 1 else 0⟩ else -1

theorem generator_value : (ringEquiv a) (generator a) = root a := by
  by_cases hd : 1 < 2^a
  · let i₁ : Fin (2^a) := ⟨1, hd⟩
    change eval a (generator a).coeffs = _
    simp only [eval_sum, generator, hd, ↓reduceIte]
    rw [Finset.sum_eq_single i₁]
    · simp [i₁]
    · intro k _ hne
      have h : k.val ≠ 1 := fun h => hne (Fin.ext h)
      simp only [h, ↓reduceIte, map_zero, zero_mul]
    · simp
  · simp only [generator, hd, ↓reduceIte, map_neg, map_one]
    have he : 2^a = 1 := by have := pow_pos (by decide : 0 < 2) a; omega
    simpa only [he, pow_one] using (root_pow a).symm

def half (a : ℕ) : Number a := ofBase a (Dyadic.ofIntWithPrec 1 1)

theorem half_two : half a * 2 = 1 := by
  apply (ringEquiv a).injective
  rw [map_mul, map_ofNat, map_one]
  change value (ofBase a _) * 2 = _
  rw [value_ofBase, ← map_ofNat (algebraMap Dyadic (Extension a)) 2, ← map_mul]
  have h : Dyadic.ofIntWithPrec 1 1 * 2 = 1 := by decide
  rw [h, map_one]

/-- Enumerating powers of the generator gives the invertible Vandermonde
differences used to construct a finite binary repair table. -/
theorem node_differences {W : ℕ} (hW : W ≤ 2^(a+1)) :
    Pairwise fun i j : Fin W => IsUnit (generator a ^ i.val - generator a ^ j.val) := by
  have hu : IsUnit (2 : Dyadic) :=
    isUnit_iff_exists_inv'.mpr ⟨Dyadic.ofIntWithPrec 1 1, by decide⟩
  have hs : ∑ i ∈ Finset.range 2, (-1 : Dyadic)^i = 0 := by simp
  have h := OAI.LinearAlgebra.FiniteFourier.primeCyclotomicNodes_pairwise_of_sum
    (ζ := (-1 : Dyadic)) (p := 2) a hu (by simp) hs hW
  intro i j hij
  have hv := (h hij).map (ringEquiv a).symm.toRingHom
  have hgen : (ringEquiv a).symm (root a) = generator a :=
    (ringEquiv a).symm_apply_eq.mpr generator_value.symm
  simpa only [map_sub, map_pow, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    ← hgen, root] using hv

end Number
end CyclotomicCode

end NearSquareRoot
end Computability
end OAI
