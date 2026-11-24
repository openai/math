import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# A finite slice field and its defining polynomial

Section 8.2 uses the smallest positive extension degree of the prime field
whose cardinality `Q` exceeds twice the point-count bound `N`. A monic
irreducible polynomial gives a presentation of that extension, using at most
`2 log₂ Q` bits for all coefficients below its leading term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceField

open Polynomial

/-- Smallest positive degree giving a prime-power cardinality above `2 * N`. -/
def extensionDegree (p N : ℕ) := Nat.log p (2 * N) + 1

/-- The selected extension of the prime field. -/
abbrev FieldOf (p N : ℕ) [Fact p.Prime] := GaloisField p (extensionDegree p N)

theorem field_card (p N : ℕ) [Fact p.Prime] :
    Nat.card (FieldOf p N) = p ^ extensionDegree p N :=
  GaloisField.card p _ (Nat.succ_ne_zero _)

theorem field_card_gt (p N : ℕ) [Fact p.Prime] : 2 * N < Nat.card (FieldOf p N) := by
  rw [field_card]
  exact Nat.lt_pow_succ_log_self (Fact.out : p.Prime).one_lt _

theorem extensionDegree_minimal (p : ℕ) [Fact p.Prime] {N e : ℕ} (hN : 0 < N)
    (h : 2 * N < p ^ e) : extensionDegree p N ≤ e :=
  (Nat.log_lt_iff_lt_pow (Fact.out : p.Prime).one_lt (by positivity : 2 * N ≠ 0)).mpr h

theorem field_card_le (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : 0 < N) :
    Nat.card (FieldOf p N) ≤ 2 * N * p := by
  rw [field_card, extensionDegree, pow_succ]
  exact Nat.mul_le_mul_right _ (Nat.pow_log_le_self _ (by positivity))

/-- Embed the advised field in the ambient algebraic closure for the hyperplane cuts. -/
noncomputable def embed (p N : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (ZMod p) E]
    [IsAlgClosed E] : FieldOf p N →ₐ[ZMod p] E :=
  IsAlgClosed.lift

/-- Read the low coefficients of a monic polynomial from fixed-width binary words. -/
noncomputable def polynomialOfBits (p e : ℕ) (bits : Fin (e * Nat.clog 2 p) → Bool) : (ZMod p)[X] :=
  let words := (RAMSerialization.arrayBits e (Nat.clog 2 p)).symm bits
  X ^ e + ∑ i : Fin e, C ((words i).val : ZMod p) * X ^ i.val

/-- The field description encodes the minimal polynomial of a power-basis generator
and hence defines the selected field up to prime-field algebra isomorphism. -/
theorem exists_polynomial_advice (p N : ℕ) [Fact p.Prime] :
    let e := extensionDegree p N
    ∃ bits : Fin (e * Nat.clog 2 p) → Bool,
      let f := polynomialOfBits p e bits
      f.Monic ∧ Irreducible f ∧ f.natDegree = e ∧ Nonempty (AdjoinRoot f ≃ₐ[ZMod p] FieldOf p N) := by
  let e := extensionDegree p N
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) (FieldOf p N)
  let f := minpoly (ZMod p) pb.gen
  have hdeg : f.natDegree = e := pb.natDegree_minpoly.trans <|
    pb.finrank.symm.trans (GaloisField.finrank p (Nat.succ_ne_zero _))
  have hmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  let words (i : Fin e) : BurstRAM.Word (Nat.clog 2 p) :=
    ⟨(f.coeff i.val).val, (ZMod.val_lt _).trans_le (Nat.le_pow_clog (by decide) _)⟩
  let bits := RAMSerialization.arrayBits _ _ words
  have hbits : polynomialOfBits p e bits = f := by
    rw [polynomialOfBits]
    simp only [bits, Equiv.symm_apply_apply, words, ZMod.natCast_zmod_val]
    conv_rhs => rw [hmonic.as_sum, hdeg]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun i ↦ C (f.coeff i) * X ^ i) _
  refine ⟨bits, ?_⟩
  change (polynomialOfBits p e bits).Monic ∧ _
  rw [hbits]
  exact ⟨hmonic, minpoly.irreducible pb.isIntegral_gen, hdeg,
    ⟨AdjoinRoot.equiv' f pb (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (minpoly.aeval _ _)⟩⟩

/-- The complete binary advice for the monic polynomial has length at most twice
the base-two logarithm of the cardinality of the selected field. -/
theorem advice_length_le (p N : ℕ) [Fact p.Prime] :
    extensionDegree p N * Nat.clog 2 p ≤ 2 * Nat.log 2 (Nat.card (FieldOf p N)) := by
  let e := extensionDegree p N
  have hp := (Fact.out : p.Prime).two_le
  have hlog : 1 ≤ Nat.log 2 p := Nat.le_log_of_pow_le (by decide) (by simpa using hp)
  have hclog : Nat.clog 2 p ≤ Nat.log 2 p + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p).le
  have hexp : Nat.log 2 p * e ≤ Nat.log 2 (p ^ e) := by
    apply Nat.le_log_of_pow_le (by decide)
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.pow_log_le_self _ (by omega)) _
  rw [field_card]
  change e * Nat.clog 2 p ≤ 2 * Nat.log 2 (p ^ e)
  calc
    _ ≤ e * (2 * Nat.log 2 p) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (Nat.log 2 p * e) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hexp

end SliceField

end VPVNP
end Computability
end OAI
