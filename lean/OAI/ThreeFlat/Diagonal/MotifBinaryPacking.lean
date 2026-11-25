import OAI.Computability.QuantumFactoring.BitEncoding
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Binary layout of variable-width tile payloads

Payload words at one port are stored little-endian, in copy order, with no
gaps. The ordinal of a bit is the sum of the preceding widths plus its
index in the current copy. Empty payload words consume no space.
-/

namespace ThreeFlat.Diagonal.MotifBinaryPacking

open scoped BigOperators

/-- The literal bit probes associated with a word of any width. -/
def word (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (ExactQuantumFactoring.bitsEquiv n).trans BitVec.equivFin.toEquiv

variable {r : ℕ} (w : Fin r → ℕ)

/-- Contiguous flattening of the individual bit vectors. -/
def flatten : ((i : Fin r) → Fin (w i) → Bool) ≃ (Fin (∑ i, w i) → Bool) where
  toFun v k := let q : (i : Fin r) × Fin (w i) := finSigmaFinEquiv.symm k
               v q.1 q.2
  invFun x i j := x (finSigmaFinEquiv ⟨i,j⟩)
  left_inv v := by
    funext i j
    let f (q : (i : Fin r) × Fin (w i)) := v q.1 q.2
    exact congrArg f (finSigmaFinEquiv.symm_apply_apply ⟨i,j⟩)
  right_inv x := by
    funext k
    apply congrArg x
    exact finSigmaFinEquiv.apply_symm_apply k

/-- A reversible packing of variable-width words exposing the address map. -/
def pack : ((i : Fin r) → Fin (2^w i)) ≃ Fin (2^∑ i, w i) :=
  ((Equiv.piCongrRight (fun i => (word (w i)).symm)).trans (flatten w)).trans (word (∑ i, w i))

@[simp] theorem unpack_bit (a : Fin (2^∑ i, w i)) (i : Fin r) (j : Fin (w i)) :
    (word (w i)).symm ((pack w).symm a i) j =
      (word (∑ i, w i)).symm a (finSigmaFinEquiv ⟨i,j⟩) := by
  change (word (w i)).symm (word (w i) _) j = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem packed_bit (a : (i : Fin r) → Fin (2 ^ w i)) (i : Fin r) (j : Fin (w i)) :
    (word (∑ i, w i)).symm (pack w a) (finSigmaFinEquiv ⟨i,j⟩) = (word (w i)).symm (a i) j := by
  rw [← unpack_bit, Equiv.symm_apply_apply]

/-- The physical bit address before adding the parent port's base. -/
theorem bit_offset (i : Fin r) (j : Fin (w i)) :
    (finSigmaFinEquiv (n := w) ⟨i,j⟩).val = (∑ t : Fin i.val, w (Fin.castLE i.isLt.le t)) + j.val :=
  finSigmaFinEquiv_apply _

end ThreeFlat.Diagonal.MotifBinaryPacking

end OAI
