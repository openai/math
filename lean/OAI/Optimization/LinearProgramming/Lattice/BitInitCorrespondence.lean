import OAI.Optimization.LinearProgramming.Lattice.BitState
import OAI.Optimization.LinearProgramming.Lattice.LLLLoopNative
import OAI.Optimization.LinearProgramming.Lattice.NativeStoredBits
import HexGramSchmidtMathlib.Int.Augmented
import HexGramSchmidtMathlib.Int.Swap

/-! The packed native LLL initializer expressed by ordinary integer Gram minors.
Kim Morrison's Hex Gram–Schmidt formalization (© 2026 Lean FRO, LLC, Apache-2.0)
supplies the determinant identities for
[scaled coefficients](https://github.com/leanprover/hex-gram-schmidt-mathlib/blob/c5c8f0561e94b06af7a05e2938ecdc07bc02d325/HexGramSchmidtMathlib/Int/Augmented.lean#L1087)
and [leading Gram minors](https://github.com/leanprover/hex-gram-schmidt-mathlib/blob/c5c8f0561e94b06af7a05e2938ecdc07bc02d325/HexGramSchmidtMathlib/Int/Swap.lean#L643). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal

/-- Row dot product on the list representation; the first argument determines the width. -/
def gramDotAt (A : IntMatrix) (r s : ℕ) : ℤ :=
  ∑ t : Fin (rowAt A r).length, entryAt A r t.val * entryAt A s t.val

/-- The dot product is the sum over the ordinary range of column indices, the
form used by the uniform list program. -/
theorem gramDotAt_eq_range_sum (A : IntMatrix) (r s : ℕ) : gramDotAt A r s =
    ((List.range (rowAt A r).length).map
      (fun k => readAt 0 (rowAt A r) k * readAt 0 (rowAt A s) k)).sum := by
  have h (n : ℕ) (f : ℕ → ℤ) : (∑ i : Fin n, f i.val) = ((List.range n).map f).sum := by
    induction n with
    | zero => simp
    | succ n ih => rw [Fin.sum_univ_castSucc, List.range_succ]; simp [ih]
  exact h (rowAt A r).length (fun k => readAt 0 (rowAt A r) k * readAt 0 (rowAt A s) k)

/-- Rows 0,...,j-1,i and columns 0,...,j of the symmetric row Gram matrix. -/
def mixedGramMatrix (A : IntMatrix) (i j : ℕ) : Matrix (Fin (j+1)) (Fin (j+1)) ℤ :=
  fun a b => gramDotAt A (if a.val < j then a.val else i) b.val

noncomputable def mixedGramDet (A : IntMatrix) (i j : ℕ) : ℤ :=
  (mixedGramMatrix A i j).det

/-- The state for the bit-stack initializer. This list definition also specifies its
answer on ragged input; the correspondence below is unconditional on rectangular matrices. -/
noncomputable def mixedGramInitializer (A : IntMatrix) : State :=
  (A, List.ofFn (fun i : Fin A.length => List.ofFn (fun j : Fin A.length =>
        if i.val < j.val then 0 else mixedGramDet A i.val j.val)),
    1 :: List.ofFn (fun i : Fin A.length => (mixedGramDet A i.val i.val).toNat))

theorem gramDotAt_packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) (i j : Fin n) :
    gramDotAt (packMatrix A) i.val j.val = (A.row i).dotProduct (A.row j) := by
  unfold gramDotAt
  rw [rowAt_packMatrix, length_packVector, HexMatrixMathlib.dotProduct_eq]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro k _
  rw [entryAt_packMatrix, entryAt_packMatrix]
  simp only [HexMatrixMathlib.vectorEquiv_apply, Hex.Matrix.getElem_row]
  rfl

private theorem row_dot_comm {n m : ℕ} (A : Hex.Matrix ℤ n m) (a b : Fin n) :
    (A.row a).dotProduct (A.row b) = (A.row b).dotProduct (A.row a) := by
  rw [HexMatrixMathlib.dotProduct_eq, HexMatrixMathlib.dotProduct_eq, dotProduct_comm]

theorem mixedGramDet_diagonal {n m : ℕ} (A : Hex.Matrix ℤ n m) (i : Fin n) :
    mixedGramDet (packMatrix A) i.val i.val =
      (Hex.GramSchmidt.Int.gramDet A (i.val+1) i.isLt : ℤ) := by
  let G := Hex.GramSchmidt.leadingGramMatrixInt A (i.val+1) i.isLt
  have hM : mixedGramMatrix (packMatrix A) i.val i.val = HexMatrixMathlib.matrixEquiv G := by
    ext a b
    let r : Fin n := ⟨a.val,a.isLt.trans_le i.isLt⟩
    let c : Fin n := ⟨b.val,b.isLt.trans_le i.isLt⟩
    have he : (if a.val < i.val then a.val else i.val) = a.val := by split <;> omega
    rw [show mixedGramMatrix (packMatrix A) i.val i.val a b =
      gramDotAt (packMatrix A) (if a.val < i.val then a.val else i.val) b.val from rfl, he]
    change gramDotAt (packMatrix A) r.val c.val = _
    rw [gramDotAt_packMatrix,HexMatrixMathlib.matrixEquiv_apply]
    simp only [G,Hex.GramSchmidt.leadingGramMatrixInt,Hex.Matrix.getElem_ofFn]
    rfl
  calc
    _ = (HexMatrixMathlib.matrixEquiv G).det := congrArg Matrix.det hM
    _ = Hex.Matrix.det G := (HexMatrixMathlib.det_eq G).symm
    _ = _ := Hex.GramSchmidt.Int.leadingGramMatrixInt_det_eq_gramDet_int A (i.val+1) i.isLt

theorem mixedGramDet_lower {n m : ℕ} (A : Hex.Matrix ℤ n m) (i j : Fin n) (hji : j < i) :
    mixedGramDet (packMatrix A) i.val j.val =
    ((Hex.GramSchmidt.Int.scaledCoeffs A).getRow i).get j := by
  let G := Hex.GramSchmidt.scaledCoeffMatrix A i j hji
  have hM : (mixedGramMatrix (packMatrix A) i.val j.val).transpose = HexMatrixMathlib.matrixEquiv G := by
    ext a b
    let r : Fin n := ⟨a.val,a.isLt.trans_le j.isLt⟩
    let c : Fin n := ⟨b.val,b.isLt.trans_le j.isLt⟩
    rw [Matrix.transpose_apply,HexMatrixMathlib.matrixEquiv_apply]
    simp only [mixedGramMatrix,G,Hex.GramSchmidt.scaledCoeffMatrix,Hex.Matrix.getElem_ofFn]
    by_cases hb : b.val = j.val
    · have hbl : ¬ b.val < j.val := by omega
      rw [ite_eq_right hbl, ite_eq_left hb]
      change gramDotAt (packMatrix A) i.val r.val = (A.row r).dotProduct (A.row i)
      rw [gramDotAt_packMatrix,row_dot_comm]
    · have hbl : b.val < j.val := by have := b.isLt; omega
      rw [ite_eq_left hbl, ite_eq_right hb]
      change gramDotAt (packMatrix A) c.val r.val = (A.row r).dotProduct (A.row c)
      rw [gramDotAt_packMatrix,row_dot_comm]
  calc
    _ = (mixedGramMatrix (packMatrix A) i.val j.val).transpose.det := (Matrix.det_transpose _).symm
    _ = (HexMatrixMathlib.matrixEquiv G).det := congrArg Matrix.det hM
    _ = Hex.Matrix.det G := (HexMatrixMathlib.det_eq G).symm
    _ = _ := by
      exact_mod_cast (Hex.GramSchmidt.Int.scaledCoeffs_lower_eq_det_scaledCoeffMatrix A i j hji).symm

private theorem mixedGram_nu {n m : ℕ} (A : Hex.Matrix ℤ n m) (i j : Fin n) :
    (if i.val < j.val then 0 else mixedGramDet (packMatrix A) i.val j.val) =
      ((LLLState.ofBasis A).ν.getRow i).get j := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [ite_eq_left h]
    exact (Hex.GramSchmidt.Int.scaledCoeffs_upper A i.val j.val i.isLt j.isLt h).symm
  · have he : i = j := Fin.ext h
    subst j
    rw [ite_eq_right (lt_irrefl _),mixedGramDet_diagonal]
    exact (Hex.GramSchmidt.Int.scaledCoeffs_diag A i.val i.isLt).symm
  · rw [ite_eq_right (not_lt.mpr h.le)]
    exact mixedGramDet_lower A i j h

/-- Computing the list of these Gram minors gives exactly the concrete native LLL state,
with the same integer coefficients and the same determinant vector, even on singular inputs. -/
theorem mixedGramInitializer_packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) :
    mixedGramInitializer (packMatrix A) = packState (LLLState.ofBasis A) := by
  unfold mixedGramInitializer
  rw [length_packMatrix]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    exact mixedGram_nu A i j
  · change _ = List.ofFn (fun j : Fin (n+1) => (LLLState.ofBasis A).d.get j)
    rw [List.ofFn_succ]
    have hv := HexLLLMathlib.LLLState.ofBasis_valid A
    apply congrArg₂ List.cons
    · have h := hv.d_eq 0 (by omega)
      simpa [Hex.GramSchmidt.Int.gramDet_zero] using h.symm
    · apply congrArg List.ofFn
      funext i
      rw [mixedGramDet_diagonal,Int.toNat_natCast]
      exact (hv.d_eq i.succ.val i.succ.isLt).symm

/-- Bit length of every entry of the initialized coefficient packet, including the
diagonal and the unused upper triangle. -/
theorem initial_nu_entry_size {n m L : ℕ} (A : Hex.Matrix ℤ n m)
    (hB : ∀ i j, ((HexMatrixMathlib.matrixEquiv A) i j).natAbs ≤ 2^L) (i j : Fin n) :
    (((LLLState.ofBasis A).ν.getRow i).get j).natAbs.size ≤ (n+m+2*L)*n+1 := by
  rcases lt_trichotomy i.val j.val with hij | hij | hji
  · rw [← mixedGram_nu,ite_eq_left hij]
    simp
  · have he : i = j := Fin.ext hij
    subst j
    rw [← mixedGram_nu,ite_eq_right (lt_irrefl _),mixedGramDet_diagonal,Int.natAbs_natCast]
    have hd := nativePrefixGram A i.succ
    have hh := hd.le.trans (prefixGramMagnitude_le _ hB i.succ)
    simpa only [Fin.val_succ,Nat.size_pow] using Nat.size_le_size hh
  · apply native_scaled_coefficient_bits _ (HexLLLMathlib.LLLState.ofBasis_valid A) _ _ _ hji
    intro r c
    have hb := hB r c
    rw [HexMatrixMathlib.matrixEquiv_apply] at hb
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hb

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
