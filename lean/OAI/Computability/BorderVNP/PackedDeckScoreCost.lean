import OAI.Computability.BorderVNP.PackedDeckChoiceCircuit

/-! # Output-linear bit costs of one conditional deck digit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckScore

/-- Sorting-and-scan overhead is cubic in the index and record widths per physical lane. -/
theorem queryCost_le (b k w : ℕ) : queryCost b k w ≤ 2^b * (150*(b+k+w+1)^3) := by
  unfold queryCost
  apply Nat.mul_le_mul_left
  ring_nf
  omega

/-- Logarithmic batch widths together with the numerical input width control all score words. -/
def workBits (B G H : Type*) [Fintype B] [Fintype G] [Fintype H] (k w : ℕ) :=
  batchBits G H + batchBits (B × H) Unit + k + w + 1

private theorem padded_le (U Q : Type*) [Fintype U] [Fintype Q] :
    2^(batchBits U Q) ≤ 2*(Fintype.card U + Fintype.card Q + 1) := by
  by_cases h : 0 < Fintype.card U + Fintype.card Q
  · exact (PackedHistogram.layout_size U Q h).le.trans (by omega)
  · have hz : Fintype.card U + Fintype.card Q = 0 := by omega
    simp [batchBits, hz]

/-- A per-child estimate linear in the tile counts, up to a polynomial in the input word
width and the logarithms of the batch lengths. The factor involving the number of relative
bins is fixed throughout the product-cover tower. -/
theorem childCost_le (B G H : Type*) [Fintype B] [Fintype G] [Fintype H] (k w C e : ℕ) :
    childCost B G H k w C e ≤
      2 + 600*Fintype.card B*(Fintype.card G+Fintype.card H+1)*(workBits B G H k w)^3 +
      Fintype.card B*Fintype.card H*C*(w+1)^e +
      2400*(Fintype.card B*Fintype.card H+2)*(workBits B G H k w)^3 := by
  let b₁ := batchBits G H
  let b₂ := batchBits (B × H) Unit
  let L := workBits B G H k w
  have h₁ : b₁+k+w+1 ≤ L := by simp [b₁, L, workBits]
  have hwidth : scoreBits B H w = 2*w+b₂ := by simp [sumBits, batchBits, b₂]
  have h₂ : b₂+0+scoreBits B H w+1 ≤ 2*L := by rw [hwidth]; dsimp [L,workBits,b₂]; omega
  have q₁ : queryCost b₁ k w ≤ (2*(Fintype.card G + Fintype.card H + 1))*(150*L^3) :=
    (queryCost_le ..).trans (Nat.mul_le_mul (padded_le G H)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₁ _)))
  have q₂ : queryCost b₂ 0 (scoreBits B H w) ≤
      (2*(Fintype.card B*Fintype.card H+2))*(150*(2*L)^3) := by
    apply (queryCost_le ..).trans
    apply Nat.mul_le_mul _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₂ _))
    simpa only [Fintype.card_prod, Fintype.card_unit, Nat.add_assoc] using padded_le (B × H) Unit
  change 1 + (2*Fintype.card B)*queryCost b₁ k w +
    (1 + Fintype.card (B × H)*(C*(w+1)^e) + queryCost b₂ 0 (scoreBits B H w)) ≤ _
  calc
    _ ≤ 1 + (2*Fintype.card B)*((2*(Fintype.card G+Fintype.card H+1))*(150*L^3)) +
        (1 + Fintype.card (B × H)*(C*(w+1)^e) + (2*(Fintype.card B*Fintype.card H+2))*(150*(2*L)^3)) := by
      gcongr
    _ = _ := by simp only [Fintype.card_prod, L]; ring

end PackedDeckScore

end BorderVNP
end Computability
end OAI
