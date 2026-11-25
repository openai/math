import OAI.Optimization.LinearProgramming.Compression.MinorLoadInput
import OAI.Optimization.LinearProgramming.Compression.Elimination

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

/-- One polynomial in the original input length covers every selected helper and every
original matrix scalar. The statement applies to both selectors and to empty minors. -/
theorem rationalPairRegisterBounds {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) ℚ)
    (E : Matrix (Fin rE) (Fin n) ℚ) (u : PairMinorIndex rD rE n) (hr : rD+rE=n) :
    let L := matrixEncodingLength D + matrixEncodingLength E
    let v := pairLayout D E u
    let P := fun q => ratBits q ≤ 40*(L+1)^4
    P 0 ∧ P 1 ∧ (∀ x, P x → P (-x)) ∧ (∀ i j, P (D i j)) ∧ (∀ i j, P (E i j)) ∧
      ∀ t<v.k, ∀ r : BirdRegister v.k,
        P (r.read (v.matrix.submatrix v.row v.col) (birdLayer (v.matrix.submatrix v.row v.col) t)) := by
  let L := matrixEncodingLength D + matrixEncodingLength E
  let v := pairLayout D E u
  have hlen {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℚ) : a*b ≤ matrixEncodingLength A := by
    calc
      a*b = ∑ _ : Fin a, ∑ _ : Fin b, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (show 1 ≤ RAM.ratBits (A i j) by unfold RAM.ratBits; omega)
  have hn : n ≤ L := calc
    n ≤ n*n := Nat.le_mul_self _
    _ = rD*n+rE*n := by rw [← Nat.add_mul,hr]
    _ ≤ L := Nat.add_le_add (hlen D) (hlen E)
  have hk : v.k ≤ n := by
    rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩ <;> exact (show k.val ≤ n by omega)
  have hd (i j) : ratBits (D i j) ≤ L := (matrix_entry_bits_le D i j).trans (Nat.le_add_right ..)
  have he (i j) : ratBits (E i j) ≤ L := (matrix_entry_bits_le E i j).trans (Nat.le_add_left ..)
  have hsub (i j) : ratBits ((v.matrix.submatrix v.row v.col) i j) ≤ L := by
    rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩
    · exact hd _ _
    · exact he _ _
  have hcap : L ≤ 40*(L+1)^4 := by ring_nf; omega
  have h3 : 3 ≤ 40*(L+1)^4 := by ring_nf; omega
  refine ⟨h3,h3,fun x hx => ?_,fun i j => (hd i j).trans hcap,fun i j => (he i j).trans hcap,?_⟩
  · change ratBits (-x) ≤ _
    simpa [ratBits] using hx
  · change ∀ t<v.k, ∀ r : BirdRegister v.k, ratBits (r.read (v.matrix.submatrix v.row v.col)
      (birdLayer (v.matrix.submatrix v.row v.col) t)) ≤ 40*(L+1)^4
    intro t ht r
    calc
      _ ≤ 3 + (v.k+L+2*L*v.k^2+3)*(t+2) := birdRegister_bits _ hsub t r
      _ ≤ 3 + (L+L+2*L*L^2+3)*(L+2) := by gcongr <;> omega
      _ ≤ 40*(L+1)^4 := by ring_nf; omega

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
