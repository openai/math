import OAI.Computability.BorderVNP.PackedHistogramQueries
import OAI.Computability.BorderVNP.PackedHistogramDeck
import OAI.Computability.BorderVNP.StackFrameArithmetic
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-! # Shared full-width binary dot products for the conditional deck scores -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckScore

open PackedHistogram ParseBatchLookup ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {I σ : Type*} [Fintype I] [Fintype σ] {w : ℕ}

/-- The explicit per-batch gate count for direct source and request pins. -/
def queryCost (b k w : ℕ) : ℕ := 2^b * ((k+1+w) + ((w+b)+1+k) +
    b^2*(24*((w+b)+1+k)+1) + w*(60*k+16*w+33) + b^2*(24*(w+b)+1))

/-- Binary address width for a padded batch with these two kinds of rows. -/
def batchBits (U Q : Type*) [Fintype U] [Fintype Q] := Nat.clog 2 (Fintype.card U + Fintype.card Q)

/-- Width sufficient to sum every full-width unsigned product. -/
def sumBits (I : Type*) [Fintype I] (s : ℕ) := s + Nat.clog 2 (Fintype.card I + 1)

private theorem zeros (k : ℕ) : value (fun _ : Fin k => false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [value] using ih

private def extended (s : ℕ) (i : I) : Fin (sumBits I s) → Expr (I × Fin s) :=
  prepend (fun _ : Fin (Nat.clog 2 (Fintype.card I + 1)) => .const false) (fun j : Fin s => .input (i,j))

private theorem extended_value (s : ℕ) (i : I) (x : I × Fin s → Bool) :
    wordValue x (extended s i) = value (fun j => x (i,j)) := by
  have h := prepend_map (StatementCircuit.Expr.eval x)
    (fun _ : Fin (Nat.clog 2 (Fintype.card I + 1)) => (StatementCircuit.Expr.const false : Expr (I × Fin s)))
    (fun j : Fin s => StatementCircuit.Expr.input (i,j))
  exact (congrArg value h).trans (by simp [value_prepend, Function.comp_def, StatementCircuit.Expr.eval, zeros])

private theorem extended_size (s : ℕ) (i : I) (j : Fin (sumBits I s)) : (extended s i j).size = 1 := by
  let h := prepend_map StatementCircuit.Expr.size
    (fun _ : Fin (Nat.clog 2 (Fintype.card I + 1)) => (StatementCircuit.Expr.const false : Expr (I × Fin s)))
    (fun j : Fin s => StatementCircuit.Expr.input (i,j))
  have he := prepend_map (fun _ : Unit => (1:ℕ)) (fun _ : Fin (Nat.clog 2 (Fintype.card I+1)) => ())
    (fun _ : Fin s => ())
  exact congrFun (h.trans he.symm) j

/-- Sum all lanes in one circuit, with leading zero extension preventing overflow. -/
noncomputable def sumFrame (I : Type*) [Fintype I] (s : ℕ) :
    Frame (I × Fin s) (Fin (sumBits I s)) :=
  (queries (layout I Unit) (fun _ (j : Fin 0) => j.elim0) (extended s)
    (fun _ (j : Fin 0) => j.elim0)).select (fun j => ((),j))

theorem sumFrame_size (I : Type*) [Fintype I] (s : ℕ) :
    (sumFrame I s).size ≤ queryCost (batchBits I Unit) 0 (sumBits I s) := by
  simp only [sumFrame, Frame.select_size]
  simpa only [queryCost, batchBits, Nat.mul_one] using queries_size (layout I Unit)
    (fun _ (j : Fin 0) => j.elim0) (extended s) (fun _ (j : Fin 0) => j.elim0) 1 le_rfl
    (fun _ j => j.elim0) (fun i j => (extended_size s i j).le) (fun _ j => j.elim0)

/-- The summation circuit is exact for every input assignment. -/
theorem sumFrame_value (I : Type*) [Fintype I] (s : ℕ) (x : I × Fin s → Bool) :
    value ((sumFrame I s).eval x) = ∑ i, value (fun j => x (i,j)) := by
  have cap : (∑ i : I, value (fun j => x (i,j))) < 2^(sumBits I s) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (value_lt (fun j => x (i,j))).le)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    apply h.trans_lt
    rw [sumBits, pow_add, Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide : 1 < 2) _)) (Nat.two_pow_pos s)
  let keys := fun (_ : I) (j : Fin 0) => (j.elim0 : Expr (I × Fin s))
  let qs := fun (_ : Unit) (j : Fin 0) => (j.elim0 : Expr (I × Fin s))
  have hzero (f : Fin 0 → Expr (I × Fin s)) : wordValue x f = 0 := rfl
  have hfit (a : ℕ) : (∑ i, if wordValue x (keys i) = a then wordValue x (extended s i) else 0) < 2^(sumBits I s) := by
    by_cases ha : a = 0
    · simpa only [hzero, ha, ite_true, extended_value] using cap
    · simp [hzero, Ne.symm ha]
  have h := queries_value (layout I Unit) keys (extended s) qs x hfit ()
  have he : (sumFrame I s).eval x = fun j => (queries (layout I Unit) keys (extended s) qs).eval x ((),j) :=
    funext fun j => Frame.select_eval _ _ _ _
  rw [he, h]
  simp only [hzero, ite_true, extended_value]

/-- One independent full-width multiplication per lane, followed by the exact shared sum. -/
theorem dotFrames :
    ∃ C e : ℕ, ∀ (I : Type*) [Fintype I] (w : ℕ),
      ∃ f : Frame (I × (Fin w ⊕ Fin w)) (Fin (sumBits I (2*w))),
        f.size ≤ 1 + Fintype.card I*(C*(w+1)^e) + queryCost (batchBits I Unit) 0 (sumBits I (2*w)) ∧
        ∀ x, value (f.eval x) = ∑ i, value (fun j => x (i,.inl j)) * value (fun j => x (i,.inr j)) := by
  obtain ⟨C,e,mult⟩ := StackFrame.multiplicationFrames
  refine ⟨C,e,?_⟩
  intro I inst w
  obtain ⟨f,hf,he⟩ := mult w
  let row (i : I) : Frame (I × (Fin w ⊕ Fin w)) (Fin (2*w)) := f.subst (Frame.initial (fun j => (i,j)))
  obtain ⟨all,ha,hw⟩ := Crossing.exists_parallelFrames (out := fun _ : I => Fin (2*w)) row
  let product := all.select fun ij : I × Fin (2*w) => ⟨ij.1,ij.2⟩
  refine ⟨(sumFrame I (2*w)).subst product, ?_, ?_⟩
  · simp only [row, Frame.subst_size, Frame.initial_size, zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ha
    simp only [Frame.subst_size, product, Frame.select_size]
    exact Nat.add_le_add (ha.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hf) _)) (sumFrame_size ..)
  · intro x
    have hval : ((sumFrame I (2*w)).subst product).eval x = (sumFrame I (2*w)).eval (product.eval x) :=
      funext fun j => Frame.subst_eval _ _ _ _
    rw [hval, sumFrame_value]
    apply Finset.sum_congr rfl
    intro i _
    have hz : (Frame.initial (fun j : Fin w ⊕ Fin w => (i,j))).eval x =
        Sum.elim (fun j => x (i,.inl j)) (fun j => x (i,.inr j)) := by
      funext j
      cases j <;> simp
    simpa only [product, Frame.select_eval, hw, row, Frame.subst_eval, hz] using
      he (fun j => x (i,.inl j)) (fun j => x (i,.inr j))

end PackedDeckScore

end BorderVNP
end Computability
end OAI
