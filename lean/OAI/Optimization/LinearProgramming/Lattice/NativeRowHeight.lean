import OAI.Optimization.LinearProgramming.Lattice.LLLNative
import OAI.Optimization.LinearProgramming.Lattice.LLLRowHeight

/-! Consecutive stored Gram determinants bound the Euclidean lengths used inside
the native size-reduction loop. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal InnerProductSpace

/-- Every Gram-determinant slot of a valid state with independent rows is positive. -/
theorem native_gram_slot_positive {n m : ℕ} (s : LLLState n m) (hs : s.Valid)
    (hind : s.b.independent) (a : Fin (n+1)) : 0 < s.d.get a := by
  rcases a with ⟨a, ha⟩
  rw [hs.d_eq a ha]
  cases a with
  | zero => simp [Hex.GramSchmidt.Int.gramDet_zero]
  | succ a => exact hind ⟨a, by omega⟩

/-- The actual integer denominator table bounds every Gram–Schmidt length and its inverse. -/
theorem native_gram_length_bounds {n m K : ℕ} (s : LLLState (n+1) m) (hs : s.Valid)
    (hind : s.b.independent) (hD : ∀ a, s.d.get a ≤ K) (i : Fin (n+1)) :
    let g := ‖gramSchmidt ℝ (Hex.GramSchmidtMathlib.intRowFamily s.b) i‖
    g ≤ K ∧ g⁻¹ ≤ K := by
  intro g
  have lo0 := native_gram_slot_positive s hs hind i.castSucc
  have lo1 := native_gram_slot_positive s hs hind i.succ
  have hrat := Hex.GramSchmidt.Int.basis_normSq s.b hind i.val i.isLt
  have hrel : g^2 = (s.d.get i.succ : ℝ) / (s.d.get i.castSucc : ℝ) := by
    rw [show g ^ 2 = ((Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b) i : ℚ) : ℝ) from
        (nativeNormSq_eq s.b i).symm,
      show s.d.get i.succ = Hex.GramSchmidt.Int.gramDet s.b (i.val+1) i.isLt from
        hs.d_eq (i.val+1) i.succ.isLt,
      show s.d.get i.castSucc = Hex.GramSchmidt.Int.gramDet s.b i.val i.isLt.le from
        hs.d_eq i.val i.castSucc.isLt]
    have hcast := congrArg (fun x : ℚ => (x : ℝ)) hrat
    push_cast at hcast
    exact hcast
  have hprev : 0 < (s.d.get i.castSucc : ℝ) := by exact_mod_cast lo0
  have hnow : 0 < (s.d.get i.succ : ℝ) := by exact_mod_cast lo1
  have hsq : 0 < g^2 := hrel ▸ div_pos hnow hprev
  have hg : 0 < g := by
    have hn : 0 ≤ g := norm_nonneg _
    by_contra! h
    have := le_antisymm h hn
    simp [this] at hsq
  exact gram_length_and_inverse_le hg (by exact_mod_cast lo1) (by exact_mod_cast lo0)
    (by exact_mod_cast hD i.succ) (by exact_mod_cast hD i.castSucc) ((eq_div_iff hprev.ne').mp hrel)

/-- After the actual `sizeReduce` pass at row k its Euclidean norm is at most
the row count times the bound for the stored Gram determinant table. -/
theorem native_sizeReduce_row_height {n m K : ℕ} (s : LLLState (n+1) m)
    (hs : s.Valid) (hind : s.b.independent) (hD : ∀ a, s.d.get a ≤ K) (k : Fin (n+1)) :
    ‖Hex.GramSchmidtMathlib.intRowFamily (s.sizeReduce k.val).b k‖ ≤ (n+1 : ℕ) * (K : ℝ) := by
  let t := s.sizeReduce k.val
  have ht : t.Valid := LLLState.sizeReduce_valid s _ hs
  have hi : t.b.independent := LLLState.sizeReduce_independent s _ hind hs ht
  have hDt : ∀ a, t.d.get a ≤ K := by
    intro a
    change (s.sizeReduce k.val).d.get a ≤ K
    rw [LLLState.sizeReduce_d]
    exact hD a
  change ‖Hex.GramSchmidtMathlib.intRowFamily t.b k‖ ≤ _
  apply sizeReduced_row_height _ _ (Nat.cast_nonneg K) (fun j => (native_gram_length_bounds t ht hi hDt j).1)
  intro j hj
  have hsred := LLLState.sizeReduce_size_reduced s k.val k.isLt hs hind j.val hj
  change 4 * (Hex.GramSchmidt.Int.coeffs t.b)[k][j] *
      (Hex.GramSchmidt.Int.coeffs t.b)[k][j] ≤ (1 : ℚ) at hsred
  have hR := (Rat.cast_le (K := ℝ)).mpr hsred
  push_cast at hR
  rw [nativeCoeff_eq t.b hj] at hR
  exact abs_le_of_sq_le_sq (by nlinarith) (by norm_num)

end Lattice
end LinearProgramming
end Optimization
end OAI
