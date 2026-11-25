import OAI.Computability.BorderVNP.ResidueEntryFieldProgram
import OAI.Computability.BorderVNP.ResiduePackedGuess
import OAI.Computability.QuantumFactoring.ArithmeticPredicates
import OAI.Computability.QuantumFactoring.WordResize
import OAI.Computability.QuantumFactoring.BooleanFold

/-! # Validity and threshold circuits for the packed residue-entry guesses

The two Boolean tests implement the rejection conditions in the multiplicative grid sum
and the final comparison with the prime-field representative. The tests use no field-sized
lookup table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryField

open ExactQuantumFactoring BitArithmetic BooleanNetwork
open ResidueFourier

variable {d w n p b : ℕ}

/-- Split a binary guess into little-endian prime-field limb words. -/
def limbWords (d w : ℕ) : (Fin (d*w) → Bool) ≃ LimbWords d w :=
  (finProdFinEquiv.symm.arrowCongr (Equiv.refl _)).trans ((Equiv.curry _ _ _).trans
    ((Equiv.refl _).arrowCongr ((bitsEquiv w).trans BitVec.equivFin.toEquiv)))

/-- The numerical value of the specified limb in the binary guess. -/
theorem limbWords_val (x : Fin (d*w) → Bool) (i : Fin d) :
    (limbWords d w x i).val = value (block x i) := rfl

/-- Circuit checking that every guessed prime-field limb is in range and at least one is nonzero. -/
def validGuess (d w p : ℕ) : BooleanNetwork (d*w) 1 :=
  (all (List.ofFn fun i => wordLt (blockNet d w i) (literal _ _ p))).band
    (any (List.ofFn fun i => wordLt (literal _ _ 0) (blockNet d w i)))

/-- Acceptance by the Boolean range check is exactly the paper's multiplicative-grid condition. -/
theorem validGuess_eval (hp : p < 2^w) (x : Fin (d*w) → Bool) :
    (validGuess d w p).eval x 0 = true ↔ validLimbs p (limbWords d w x) := by
  simp only [validGuess, eval_band, Bool.and_eq_true, all_eval, any_eval,
    List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, exists_exists_eq_and,
    wordLt_eval, decide_eq_true_eq, literal, wordConstant_eval, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Nat.zero_mod, blockNet_eval, validLimbs, limbWords_val, value,
    Nat.pos_iff_ne_zero]

/-- Bit complexity of the validity test, linear in the limb count and the limb width. -/
theorem validGuess_count (d w p : ℕ) :
    (validGuess d w p).net.count ≤ d*(49*w+9) + d*(49*w+12) + 3 := by
  let f := fun i => wordLt (blockNet d w i) (literal _ _ p)
  let g := fun i => wordLt (literal _ _ 0) (blockNet d w i)
  have h (i : Fin d) : (f i).net.count ≤ 49*w+8 := by
    have h := wordLt_count (blockNet d w i) (literal _ _ p)
    rw [blockNet_count, literal, wordConstant_count] at h
    exact h.trans (by omega)
  have h' (i : Fin d) : (g i).net.count ≤ 49*w+8 := by
    have h := wordLt_count (literal _ _ 0) (blockNet d w i)
    rw [blockNet_count, literal, wordConstant_count] at h
    exact h.trans (by omega)
  have ha := all_count (List.ofFn f) (c := 49*w+8) (by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact h i)
  have hb := any_count (List.ofFn g) (c := 49*w+8) (by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact h' i)
  rw [List.length_ofFn] at ha hb
  change ((all (List.ofFn f)).band (any (List.ofFn g))).net.count ≤ _
  rw [count_band]
  norm_num [Nat.add_assoc] at ha hb
  omega

/-- A guess accepted by the range check is the canonical encoding of the unpacked field element. -/
theorem represents_unpack [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    (B : Module.Basis (Fin d) (ZMod p) K) (x : Fin (d*w) → Bool)
    (h : validLimbs p (limbWords d w x)) :
    Represents B x (unpackScalar B (limbWords d w x)) := by
  intro i
  rw [← limbWords_val]
  change _ = (B.equivFun (B.equivFun.symm _) i).val
  rw [LinearEquiv.apply_symm_apply, ZMod.val_natCast_of_lt (h.1 i)]

/-- Widen the final threshold guess to the modulus width, and compare to the prime-field
coordinate computed by the residue-entry evaluator. -/
def threshold (y : BooleanNetwork n b) (coord : BooleanNetwork n w) : BooleanNetwork n 1 :=
  wordLt (y.comp (resizeWord b w)) coord

/-- The threshold circuit returns one exactly on guesses strictly below the representative. -/
theorem threshold_eval (hb : b ≤ w) (y : BooleanNetwork n b) (coord : BooleanNetwork n w)
    (x : Fin n → Bool) (v : ZMod p) (h : value (coord.eval x) = v.val) :
    (threshold y coord).eval x 0 = true ↔ value (y.eval x) < v.val := by
  rw [threshold, wordLt_eval, decide_eq_true_eq, eval_comp, resizeWord_toNat hb, ← h]
  rfl

/-- Cost of the threshold test above the two supplied input circuits. -/
theorem threshold_count (y : BooleanNetwork n b) (coord : BooleanNetwork n w) :
    (threshold y coord).net.count ≤ y.net.count + coord.net.count + 49*w + 8 := by
  have h := wordLt_count (y.comp (resizeWord b w)) coord
  rw [count_comp] at h
  exact h.trans (by have := resizeWord_count b w; omega)

end ResidueEntryField

end BorderVNP
end Computability
end OAI
