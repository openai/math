import OAI.Computability.VPVNP.SliceArithmeticAdvice
import OAI.Computability.VPVNP.SliceArithmeticRound
import OAI.Computability.VPVNP.RAMTapeWordSlice

/-!
# Power-basis encodings at the evaluator interface

Field values at the scalar-query boundary have canonical coefficient vectors.
The packed input to the arithmetic routines consists of those same residues
padded to the working register width. The first packed word computes the
prime-field coordinate used by the accepting-branch routine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic

open Polynomial SliceArithmeticRound BurstRAM

variable {p e w : ℕ} [Fact p.Prime]

/-- The quotient representation and canonical low-degree-first coefficient
vectors form a bijection. -/
noncomputable def valueEquiv (c : Vector p e) : Vector p e ≃ AdjoinRoot (modulus c) where
  toFun := value (modulus c)
  invFun z i := (ZMod.finEquiv p).symm
    ((AdjoinRoot.powerBasisAux' (modulus_monic c)).repr z (i.cast (modulus_natDegree c).symm))
  left_inv v := by
    funext i
    have h := congrArg (ZMod.finEquiv p).symm (repr_value (modulus_monic c) (modulus_natDegree c) v i)
    rw [cast_val_eq_finEquiv, RingEquiv.symm_apply_apply] at h
    exact h
  right_inv z := by
    let b := AdjoinRoot.powerBasisAux' (modulus_monic c)
    let v (i : Fin e) := (ZMod.finEquiv p).symm (b.repr z (i.cast (modulus_natDegree c).symm))
    apply b.repr.injective
    ext j
    obtain ⟨i, rfl⟩ := (finCongr (modulus_natDegree c).symm).surjective j
    exact (repr_value (modulus_monic c) (modulus_natDegree c) v i).trans
      ((cast_val_eq_finEquiv (v i)).trans ((ZMod.finEquiv p).apply_symm_apply _))

/-- Encode a scalar computed by the matrix-entry oracle into the chosen
polynomial basis of its actual ground field. -/
noncomputable def scalarEncoding {K : Type*} [Field K] [Algebra (ZMod p) K]
    {c : Vector p e} (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (x : K) : Vector p e :=
  (valueEquiv c).symm (φ.symm x)

@[simp] theorem map_scalarEncoding {K : Type*} [Field K] [Algebra (ZMod p) K]
    {c : Vector p e} (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (x : K) :
    φ (value (modulus c) (scalarEncoding φ x)) = x := by
  change φ (valueEquiv c ((valueEquiv c).symm (φ.symm x))) = x
  simp

/-- Arithmetic on the query result and accumulator produces the canonical
coefficient encoding of the product in the actual ground field. -/
theorem mul_scalarEncoding {K : Type*} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (x y : K) :
    mul c (scalarEncoding φ x) (scalarEncoding φ y) = scalarEncoding φ (x * y) := by
  apply (φ.injective.comp (value_injective (modulus_monic c) (modulus_natDegree c)))
  simp only [Function.comp_apply, value_mul, map_mul, map_scalarEncoding]

/-- Widening a canonical limb for modular arithmetic appends high zero bits. -/
theorem limb_padded (hw : Word.workingWidth p ≤ w) (a : Fin p) :
    wordBits (Word.limb w a) =
      wordBits (Word.limb (Nat.clog 2 p) a) ++ List.replicate (w - Nat.clog 2 p) false := by
  apply TapeWord.eq_of_length_value
  · simp only [length_wordBits, List.length_append, List.length_replicate]
    unfold Word.workingWidth at hw
    omega
  · rw [TapeWord.value_append, TapeWord.value_zeros, mul_zero, add_zero, TapeWord.value_wordBits,
      TapeWord.value_wordBits, Word.limb_val hw]
    exact (Nat.mod_eq_of_lt (a.isLt.trans_le (Nat.le_pow_clog (by decide) _))).symm

omit [Fact p.Prime] in
/-- The compact binary advice for a coefficient vector is exactly its packed
stream at the minimum coefficient width. -/
theorem packed_advice (v : Vector p e) :
    packed (Nat.clog 2 p) (List.ofFn v) = List.ofFn (encode v) := by
  let W := Nat.clog 2 p
  let limbs (i : Fin e) : BurstRAM.Word W := Word.limb W (v i)
  have h : RAMSerialization.arrayBits e W limbs = encode v := by
    apply congrArg (RAMSerialization.arrayBits e W)
    funext i
    exact Fin.ext (Nat.mod_eq_of_lt ((v i).isLt.trans_le (Nat.le_pow_clog (by decide) _)))
  rw [← h]
  have ha := List.ofFn_mul (RAMSerialization.arrayBits e W limbs)
  have hb : List.ofFn (RAMSerialization.arrayBits e W limbs) =
      (List.ofFn fun i : Fin e => List.ofFn fun j : Fin W =>
        RAMSerialization.arrayBits e W limbs (finProdFinEquiv (i, j))).flatten := by
    simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm W, Nat.add_comm] using ha
  rw [hb]
  simp only [RAMSerialization.arrayBits_at, packed, List.flatMap_def, List.map_ofFn, Function.comp_def,
    wordBits, limbs, W]

omit [Fact p.Prime] in
/-- The first complete word of a nonempty packed product is the low limb.
The terminal callback may carry arbitrary additional bits after the product. -/
theorem packed_low_limb {d : ℕ} (v : Vector p (d + 1)) (tail : List Bool) :
    packed w (List.ofFn v) ++ tail =
      wordBits (Word.limb w (v 0)) ++ (packed w (List.ofFn fun i : Fin d => v i.succ) ++ tail) := by
  rw [List.ofFn_succ]
  simp [packed]

/-- On the selected advice, reading the first word of the accumulator gives
the representative in `[0,p)` of its evaluator output. -/
theorem packed_primeCoordinate {d : ℕ} {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]
    {c : Vector p (d + 1)} (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K)
    (hc : ∀ v, SliceEvaluator.primeCoordinate p K (φ (value (modulus c) v)) =
      ((v (0 : Fin (d + 1))).val : ZMod p))
    (hw : Word.workingWidth p ≤ w) (x : K) :
    ∃ low : BurstRAM.Word w, ∃ tail : List Bool,
      packed w (List.ofFn (scalarEncoding φ x)) = wordBits low ++ tail ∧
      low.val = (SliceEvaluator.primeCoordinate p K x).val := by
  let v := scalarEncoding φ x
  refine ⟨Word.limb w (v 0), packed w (List.ofFn fun i : Fin d => v i.succ), ?_, ?_⟩
  · simpa only [List.append_nil] using packed_low_limb (w := w) v []
  · have h := hc v
    rw [map_scalarEncoding] at h
    rw [Word.limb_val hw, h, ZMod.val_natCast_of_lt (v 0).isLt]

end SliceArithmetic

end VPVNP
end Computability
end OAI
