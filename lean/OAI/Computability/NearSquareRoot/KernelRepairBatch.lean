import OAI.Computability.NearSquareRoot.KernelPencilSearch

/-! # Checked generation of the full binary repair batch

The clock rows of each shift are independent input rows. Both the physical
numbering of these rows and the order of the two check blocks are fixed
before the frequency label or the number of columns is supplied. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilSearch

open CyclotomicCode OAI.LinearAlgebra.FiniteFourier
open scoped CyclotomicCode

private instance : Encodable (ZMod 2) := inferInstanceAs (Encodable (Fin 2))

def rowCount (m h b : ℕ) : ℕ := 2^m * b^h

/-- Enumerate one row for each shift and each clock state. -/
def rowIndex (m h b : ℕ) : Signature m × Clock h b ≃ Fin (rowCount m h b) :=
  Encodable.fintypeEquivFin.trans (finCongr (by simp [Signature, Clock, rowCount, ZMod.card]))

/-- Exactly those numbered rows whose predictor multiplier is incorrect at `k`. -/
def badRows {a m h b : ℕ} [NeZero b] (A : Coefficients a m h b) (k : Signature m) :
    Finset (Fin (rowCount m h b)) :=
  ((failures A k) ×ˢ (Finset.univ : Finset (Clock h b))).map (rowIndex m h b).toEmbedding

theorem badRows_card_le {a m h b : ℕ} [NeZero b] (A : Coefficients a m h b) (hA : Good A)
    (k : Signature m) (hm : 2 ≤ m) :
    (badRows A k).card ≤ rowCount m h b / (2 * m^3) := by
  have hpos : 0 < 2*m^3 := by positivity
  have hmul := (Nat.le_div_iff_mul_le hpos).mp (hA.2 k)
  apply (Nat.le_div_iff_mul_le hpos).mpr
  simpa [badRows, rowCount, Clock, Nat.mul_right_comm] using Nat.mul_le_mul_right (b^h) hmul

theorem good_row_value {a m h b : ℕ} [NeZero b] (A : Coefficients a m h b)
    (k : Signature m) (i : Fin (rowCount m h b)) (hi : i ∉ badRows A k) :
    prediction A k ((rowIndex m h b).symm i).1 = target a k := by
  by_contra hbad
  apply hi
  apply Finset.mem_map.mpr
  exact ⟨(rowIndex m h b).symm i, Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩, Finset.mem_univ _⟩,
    (rowIndex m h b).apply_symm_apply i⟩

theorem target_sq (a : ℕ) {m : ℕ} (k : Signature m) : target a k ^ 2 = 1 := by
  rw [target, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro j _
  rw [sign, ← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]

/-- Generate the correction matrix from the tested values of the actual
pencil. The size of the matrix uses the worst-case count across signatures. -/
def correction {a m h b : ℕ} [NeZero b] (hm : 2 ≤ m)
    (hW : rowCount m h b ≤ 2^(a+1)) (A : Coefficients a m h b) (hA : Good A)
    (k : Signature m) : RepairSearch.Table (Number a) (rowCount m h b / (2*m^3)) :=
  RepairSearch.table hW (target a k) (target_sq a k)
    (fun i => prediction A k ((rowIndex m h b).symm i).1)
    (badRows A k) (badRows_card_le A hA k hm) (good_row_value A k)

theorem correction_correct {a m h b : ℕ} [NeZero b] (hm : 2 ≤ m)
    (hW : rowCount m h b ≤ 2^(a+1)) (A : Coefficients a m h b) (hA : Good A)
    {V ν : Type*} [AddCommGroup V] [Module (Number a) V] (S : V ≃ₗ[Number a] (ν → Number a))
    (sig : ν → Signature m) (P : (Fin (rowCount m h b) → V) → Fin (rowCount m h b) → V)
    (hP : ∀ x i v, S (P x i) v =
      prediction A (sig v) ((rowIndex m h b).symm i).1 * S (x i) v)
    (x : Fin (rowCount m h b) → V) (i : Fin (rowCount m h b)) :
    let s := rowCount m h b / (2*m^3)
    hermiteRepairProgram 2 (Number.half a) P S
      (repairCheck (fun i : Fin (rowCount m h b) => Number.generator a ^ i.val) s)
      ((fun k => RepairSearch.applyTable (correction hm hW A hA k)) ∘ sig) x i =
      S.symm ((target a ∘ sig) * S (x i)) :=
  RepairSearch.repaired_program hW (target a) (target_sq a)
    (fun k i => prediction A k ((rowIndex m h b).symm i).1)
    (badRows A) (fun k => badRows_card_le A hA k hm) (good_row_value A)
    S sig P hP x i

end PencilSearch

end NearSquareRoot
end Computability
end OAI
