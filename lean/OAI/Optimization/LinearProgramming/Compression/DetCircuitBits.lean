import OAI.Optimization.LinearProgramming.Compression.DetCircuit
import OAI.Optimization.LinearProgramming.Compression.Elimination
import OAI.Optimization.LinearProgramming.Compression.CircuitMachineSafe

/-! The bit bound for Bird registers applies to every subexpression in the compiled stage. -/

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

theorem allValues_sumExpr {ι K : Type} [CommRing K] (v : ι → K) (P : K → Prop)
    (k : ℕ) (f : Fin k → ArithExpr ι) (hf : ∀ i, (f i).AllValues v P)
    (hs : ∀ s : Finset (Fin k), P (∑ i ∈ s, (f i).eval v)) :
    (sumExpr k f).AllValues v P := by
  induction k with
  | zero => simpa [sumExpr, ArithExpr.AllValues] using hs ∅
  | succ k ih =>
    refine ⟨?_, hf 0, ih (fun i => f i.succ) (fun i => hf i.succ) ?_⟩
    · simpa [eval_sumExpr, Fin.sum_univ_succ] using hs Finset.univ
    · intro s
      simpa using hs (s.map (Fin.succEmb k))

/-- Each arithmetic subexpression of one entry circuit is the value of a register
(in particular an interior node of a sum is a genuine partial sum). -/
theorem birdStepExpr_registers {K : Type} [CommRing K] {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (birdStepExpr i j).AllValues (readBird A F) (fun x => ∃ r : BirdRegister n, x = r.read A F) := by
  let v := readBird A F
  let P := fun x => ∃ r : BirdRegister n, x = r.read A F
  let diag := fun k => if i < k then .read (.inr (k, k)) else (.zero : ArithExpr (BirdRead n))
  let dots := fun k => if i < k then .mul (.read (.inr (i, k))) (.read (.inl (k, j)))
    else (.zero : ArithExpr (BirdRead n))
  let I := Finset.univ.filter (i < ·)
  have hz : P 0 := ⟨.diagonal ∅, by simp [BirdRegister.read]⟩
  have di (k) : (diag k).eval v = if i < k then F k k else 0 := by
    by_cases hk : i < k <;> simp [diag, hk, ArithExpr.eval, v, readBird]
  have ds (s : Finset (Fin n)) : (∑ k ∈ s, (diag k).eval v) =
      ∑ k ∈ s.filter (i < ·), F k k := by simp only [di, Finset.sum_filter]
  have pi (k) : (dots k).eval v = if i < k then (F i k * A k j) else 0 := by
    by_cases hk : i < k <;> simp [dots, hk, ArithExpr.eval, v, readBird]
  have ps (s : Finset (Fin n)) : (∑ k ∈ s, (dots k).eval v) =
      ∑ k ∈ s.filter (i < ·), F i k * A k j := by simp only [pi, Finset.sum_filter]
  have da : (sumExpr n diag).AllValues v P := by
    refine allValues_sumExpr v P _ diag ?_ fun s => ⟨.diagonal _, ds s⟩
    intro k
    dsimp only [diag]
    split
    · exact ⟨.previous k k, rfl⟩
    · exact hz
  have pa : (sumExpr n dots).AllValues v P := by
    refine allValues_sumExpr v P _ dots ?_ fun s => ⟨.dotPartial _ i j, ps s⟩
    intro k
    dsimp only [dots]
    split
    · exact ⟨⟨.product i k j, rfl⟩, ⟨.previous i k, rfl⟩, ⟨.input k j, rfl⟩⟩
    · exact hz
  have dh : (sumExpr n diag).eval v = ∑ k ∈ I, F k k := (eval_sumExpr ..).trans (ds .univ)
  have ph : (sumExpr n dots).eval v = ∑ k ∈ I, F i k * A k j := (eval_sumExpr ..).trans (ps .univ)
  change P (-(ArithExpr.eval v (sumExpr n diag)) * A i j + (sumExpr n dots).eval v) ∧
    (P (-(ArithExpr.eval v (sumExpr n diag)) * A i j) ∧
      (P (-(ArithExpr.eval v (sumExpr n diag))) ∧ _) ∧ P (A i j)) ∧ _
  rw [dh, ph]
  exact ⟨⟨.output I I i j, rfl⟩,
    ⟨⟨.diagonalProduct I i j, rfl⟩, ⟨⟨.negDiagonal I, rfl⟩, da⟩, ⟨.input i j, rfl⟩⟩, pa⟩

/-- All intermediate rational values in the gate expression have polynomial encoding length. -/
theorem allValues_birdStepExpr {n B : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hbit : ∀ i j, RAM.ratBits (A i j) ≤ B) (t : ℕ) (i j : Fin n) :
    (birdStepExpr i j).AllValues (readBird A (birdLayer A t))
      (fun x => RAM.ratBits x ≤ 3 + (n + B + 2*B*n^2 + 3) * (t+2)) := by
  apply (birdStepExpr_registers A (birdLayer A t) i j).mono
  rintro _ ⟨r, rfl⟩
  exact birdRegister_bits A hbit t r

end Compression
end LinearProgramming
end Optimization
end OAI
