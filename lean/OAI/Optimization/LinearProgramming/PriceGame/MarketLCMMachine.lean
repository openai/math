import OAI.Optimization.LinearProgramming.PriceGame.MarketInputsMachine
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionMarketBounds

/-! # Binary LCM unit for adaptive market calls -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace InputMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open TrialExecution

noncomputable def lcmP : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun p => Nat.lcm p.1 p.2) := binaryDiv.comp (binaryMul.pair binaryGcd)

private theorem lcmBits (a b : ℕ) : (Nat.lcm a b).bits.length ≤ a.bits.length + b.bits.length := by
  have h : Nat.lcm a b ≤ a*b := by rw [Nat.lcm_eq_mul_div]; exact Nat.div_le_self _ _
  have hh : (Nat.lcm a b).bits.length ≤ (a*b).bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h
  exact hh.trans (bits_length_mul a b)

private theorem foldLcmBits (qs : List ℚ) (b : ℕ) :
    (qs.foldl (fun p q => Nat.lcm p q.den) b).bits.length ≤ b.bits.length + (listCode ratCode qs).length := by
  induction qs generalizing b with
  | nil => simp [listCode]
  | cons q qs ih =>
    have h := ih (Nat.lcm b q.den)
    have h₁ := lcmBits b q.den
    have h₂ : q.den.bits.length ≤ (ratCode q).length := by
      simp only [ratCode, prodCode, pairBits_length]; omega
    rw [List.foldl_cons, listCode_length_cons]
    omega

/-- Compute the same LCM of reduced denominators as the recursive PCG trial uses. -/
noncomputable def leastDenominatorP : Procedure (listCode ratCode) Nat.bits
    (fun qs => qs.foldl (fun p q => Nat.lcm p q.den) 1) := by
  let step : Procedure (prodCode ratCode Nat.bits) Nat.bits (fun p => Nat.lcm p.2 p.1.den) :=
    lcmP.comp ((second ratCode Nat.bits).pair (ratDen.comp (first ratCode Nat.bits)))
  let fold := foldList (0 : ℚ) step Polynomial.X (by
    intro qs b i
    rw [Polynomial.eval_X]
    change ((qs.take i).foldl (fun p q => Nat.lcm p q.den) b).bits.length ≤ _
    have hh := foldLcmBits (qs.take i) b
    have ht := listCode_length_take_le ratCode i qs
    omega)
  exact fold.comp ((identity (listCode ratCode)).pair (constant (listCode ratCode) Nat.bits 1))

private theorem lcm_spec (qs : List ℚ) (a Q : ℕ) :
    qs.foldl (fun p q => Nat.lcm p q.den) a ∣ Q ↔ a ∣ Q ∧ ∀ q ∈ qs, q.den ∣ Q := by
  induction qs generalizing a with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, ih, Nat.lcm_dvd_iff]
    simp [and_assoc]

theorem leastDenominator_agrees {ne : ℕ} (L : Fin ne → ℚ) :
    ((List.finRange ne).map L).foldl (fun p q => Nat.lcm p q.den) 1 = weightDenominator L := by
  let qs := (List.finRange ne).map L
  apply Nat.dvd_antisymm
  · apply (lcm_spec qs 1 _).2
    refine ⟨one_dvd _, ?_⟩
    intro q h
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp h
    exact den_dvd_weightDenominator L e
  · apply weightDenominator_dvd
    intro e
    have h := ((lcm_spec qs 1 _).1 (dvd_refl _)).2 (L e)
    exact h (List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩)

end InputMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
