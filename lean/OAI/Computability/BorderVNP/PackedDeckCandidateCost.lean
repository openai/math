import OAI.Computability.BorderVNP.PackedDeckCandidateBounds
import OAI.Computability.BorderVNP.PackedDeckScoreCost

/-! # Linear-in-volume gate bound for the initial finite motion comparison -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckCandidate

open PackedDeckScore

/-- Combined word and address width for the per-candidate moment, bin, and final sum stages. -/
def workBits (B G : Type*) [Fintype B] [Fintype G] (w : ℕ) :=
  batchBits B Unit + batchBits G Unit + w + 1

private theorem sumCost_le (U : Type*) [Fintype U] (s L : ℕ)
    (hl : batchBits U Unit + sumBits U s + 1 ≤ 2*L) :
    queryCost (batchBits U Unit) 0 (sumBits U s) ≤ 2400*(Fintype.card U+2)*L^3 := by
  have hp := PackedHistogram.layout_size U Unit (by simp)
  have hb : 2^batchBits U Unit ≤ 2*(Fintype.card U+2) := by
    change 2^(Nat.clog 2 (Fintype.card U + Fintype.card Unit)) ≤ _
    simp only [Fintype.card_unit] at hp ⊢
    omega
  calc
    _ ≤ 2^batchBits U Unit * (150*(batchBits U Unit+0+sumBits U s+1)^3) := queryCost_le ..
    _ ≤ (2*(Fintype.card U+2)) * (150*(2*L)^3) :=
      Nat.mul_le_mul hb (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simpa using hl) _))
    _ = _ := by ring

/-- The per-channel gate count is linear in tile volume times a polynomial in count width and
logarithmic index width, for fixed relative bin count. -/
theorem channelCost_le (B G : Type*) [Fintype B] [Fintype G] (w C e M z : ℕ) :
    let L := workBits B G w
    channelCost B G w C e M z ≤
      1 + Fintype.card B * (2 + 7200*(Fintype.card G+2)*L^3 + Fintype.card G*(C*(w+1)^e) +
        9*(M*(w+1)^z+w*(16*w+22)+1)) + 2400*(Fintype.card B+2)*L^3 := by
  intro L
  have hg (s : ℕ) (hs : s ≤ 2*w) : batchBits G Unit + sumBits G s + 1 ≤ 2*L := by
    simp only [sumBits, batchBits, Fintype.card_unit, L, workBits]
    omega
  have hb : batchBits B Unit + sumBits B w + 1 ≤ 2*L := by
    simp only [sumBits, batchBits, Fintype.card_unit, L, workBits]
    omega
  have h₁ := sumCost_le G w L (hg w (by omega))
  have h₂ := sumCost_le G (2*w) L (hg _ le_rfl)
  have h₃ := sumCost_le B w L hb
  unfold channelCost scalarCost momentCost
  calc
    _ ≤ 1 + Fintype.card B * (2 + 2*(2400*(Fintype.card G+2)*L^3) + Fintype.card G*(C*(w+1)^e) +
        2400*(Fintype.card G+2)*L^3 + 9*(M*(w+1)^z+w*(16*w+22)+1)) + 2400*(Fintype.card B+2)*L^3 := by gcongr
    _ = _ := by ring

end PackedDeckCandidate

end BorderVNP
end Computability
end OAI
