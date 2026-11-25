import OAI.Optimization.LinearProgramming.Compression.ServiceParameters
import OAI.Optimization.LinearProgramming.Compression.ServiceNumericSpec
import OAI.Optimization.LinearProgramming.Compression.ServiceInspectBounds
import OAI.Optimization.LinearProgramming.Compression.MinorLoad
import OAI.Optimization.LinearProgramming.RAM.TapeBits

/-! Binary sizes of the original rational matrices and of the actual positive
magnitudes supplied to the numerical minor solver. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceBudget
open RAM OracleSpec.MinorLog GeneratorTable

theorem dimension_le_bits {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) (hdim : d+e=n) : n ≤ totalBits (entries D++entries E) := by
  have cells {r : ℕ} (A : Matrix (Fin r) (Fin n) ℚ) : (entries A).length=r*n := by
    simp [entries,List.length_flatten,List.map_ofFn,List.sum_ofFn]
  have eq : (entries D++entries E).length=n*n := by simp [cells,← Nat.add_mul,hdim]
  exact (Nat.le_mul_self n).trans (eq ▸ entry_count_le_totalBits (entries D++entries E))

theorem magnitude_bits (q : ℚ) : ratBits |q|=ratBits q := by
  rcases le_total 0 q with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]; simp [ratBits]

/-- The scalar input of the numerical subcall consists of at most g+1 actual
determinants, even if all of them are repeated or have order zero. -/
theorem magnitudeInput_le {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) (hdim : d+e=n) (J : Finset (NonzeroPairMinor D E))
    (u : NonzeroPairMinor D E) (hg : J.card ≤ paperWidth n) :
    let input := entries D++entries E
    let values := List.ofFn (matrixMinorCache D E J u)
    n+totalBits values ≤ 20*(totalBits input+1)^10 := by
  let L := totalBits (entries D++entries E)
  let mag := matrixMinorCache D E J u
  have hn : n ≤ L := dimension_le_bits D E hdim
  have hc : J.card ≤ (L+1)^6 := hg.trans (Nat.pow_le_pow_left (by omega) _)
  have each (i : Fin (J.card+1)) : ratBits (mag i) ≤ 3+2*L^2+2*L^4 := by
    change ratBits (minorMagnitude D E (requestIndices J u i)) ≤ _
    rw [minorMagnitude,evaluatePairMinor_eq,magnitude_bits]
    simpa [L,GeneratorTable.matrixBits_public] using MinorLoad.pairMinor_bits D E (requestIndices J u i).val
  have sum : totalBits (List.ofFn mag) ≤ (J.card+1)*(3+2*L^2+2*L^4) := by
    calc
      totalBits (List.ofFn mag) = ∑ i,ratBits (mag i) := by
        simp [totalBits,List.map_ofFn,List.sum_ofFn,Function.comp_def]
        exact (Fin.sum_univ_succ (fun i : Fin (J.card+1) => ratBits (mag i))).symm
      _ ≤ ∑ _i : Fin (J.card+1), (3+2*L^2+2*L^4) := Finset.sum_le_sum (fun i _ => each i)
      _ = _ := by simp
  change n+totalBits (List.ofFn mag) ≤ 20*(L+1)^10
  calc
    _ ≤ L+((L+1)^6+1)*(3+2*L^2+2*L^4) := Nat.add_le_add hn (sum.trans
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ hc)))
    _ ≤ _ := by ring_nf; omega

end ServiceBudget
end Compression
end LinearProgramming
end Optimization
end OAI
