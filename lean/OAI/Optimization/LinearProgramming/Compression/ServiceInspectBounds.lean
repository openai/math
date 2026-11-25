import OAI.Optimization.LinearProgramming.Compression.RationalMinorSize
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM OracleSpec

/-- The polynomial helper uses exactly the binary length of the two ordinary input tapes. -/
theorem matrixBits_public {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ) :
    totalBits (MinorLog.entries D ++ MinorLog.entries E) = matrixEncodingLength D+matrixEncodingLength E := by
  simp [totalBits,MinorLog.entries,matrixEncodingLength,List.map_flatten,List.map_ofFn,List.sum_flatten,List.sum_ofFn,Function.comp_def]

private theorem cells_le_bits {d n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) : d*n ≤ matrixEncodingLength D := by
  calc
    _ = ∑ _ : Fin d,∑ _ : Fin n,1 := by simp
    _ ≤_ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (show 1 ≤ ratBits (D i j) by unfold ratBits;omega)

/-- One polynomial in actual scalar input length includes all integer staging counters,
all determinant intermediates, and one additional generator count. -/
theorem inspectHeight_bound {d e n g : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (hdim : d+e = n) (hg : g ≤ (n+1)^6) :
    let H := 50*(totalBits (MinorLog.entries D++MinorLog.entries E)+1)^6
    40*(matrixEncodingLength D+matrixEncodingLength E+1)^4 ≤ H ∧ 3+max (4*(n+1)^2) (g+1) ≤ H := by
  rw [matrixBits_public]
  let L := matrixEncodingLength D+matrixEncodingLength E
  change 40*(L+1)^4 ≤ 50*(L+1)^6 ∧ 3+max (4*(n+1)^2) (g+1) ≤ 50*(L+1)^6
  have hn : n ≤ L := calc
    n ≤ n*n := Nat.le_mul_self _
    _ = d*n+e*n := by rw [←Nat.add_mul,hdim]
    _ ≤L := Nat.add_le_add (cells_le_bits D) (cells_le_bits E)
  have low : (n+1)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) _
  have high : (n+1)^6 ≤ (L+1)^6 := Nat.pow_le_pow_left (by omega) _
  constructor
  · ring_nf;omega
  · have a : 3+4*(n+1)^2 ≤ 50*(L+1)^6 := by ring_nf at low ⊢;omega
    have c : g ≤ (L+1)^6 := hg.trans high
    have b : 3+(g+1) ≤ 50*(L+1)^6 := by ring_nf at c ⊢;omega
    rcases le_total (4*(n+1)^2) (g+1) with h | h
    · rw [max_eq_right h];exact b
    · rw [max_eq_left h];exact a

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
