import OAI.Hierarchy.DescentGLRowStageRAM

namespace OAI
/-! # A uniform clock for each of the selected-row passes -/

namespace Hierarchy.DescentGL.RowStageRAM

open ProtocolRAM

/-- This bound covers input preparation, the complete row-score bank, selection
of the least minimizing row, and construction of the new span mask. -/
def perRow (k : ℕ) : ℕ := 400*(k+1)*(2^k+1)^3

private theorem arithmetic (k N : ℕ) :
    (4+N*(2*(6+k*(2+8*N)+k*(4+N*(9+5*N)))+4))+
      ((4+N*(10+4*N*(5*N+11)))+
        ((10+24*N+94*N^2)+(4+N*(2*(16+N*(9+5*N))+4)))) ≤
      400*(k+1)*(N+1)^3 := by
  nlinarith only [Nat.zero_le k,Nat.zero_le N,Nat.zero_le (N^2),Nat.zero_le (N^3),
    Nat.zero_le (k*N),Nat.zero_le (k*N^2),Nat.zero_le (k*N^3)]

theorem ticks_le {h r : ℕ} (s : Shelf) (ptr : Fin (h+1+r) → ℕ) (bank : Fin (r+1) → ℕ) :
    ticks s ptr bank ≤ perRow (h+1+r) := by
  let k := h+1+r
  let N := 2^k
  have rk : r≤k := by dsimp [k]; omega
  have rN : 2^r≤N := Nat.pow_le_pow_right (by decide) rk
  have prep : (DescentGLInputRAM.terms ptr bank).work ≤
      6+k*(2+8*N)+k*(4+N*(9+5*N)) := by
    refine (DescentGLInputRAM.terms_work ptr bank).trans ?_
    change 6+(r+1)*(2+8*2^r)+h*(4+N*(9+5*N)) ≤ _
    have rle : r+1≤k := by dsimp [k]; omega
    have hle : h≤k := by dsimp [k]; omega
    gcongr
  have input : 4+N*(2*(DescentGLInputRAM.terms ptr bank).work+4) ≤
      4+N*(2*(6+k*(2+8*N)+k*(4+N*(9+5*N)))+4) := by gcongr
  have score := DescentGLScoreRAM.work k s.data
  have choose := RowRAM.clock_bound ⟨s.mask,k⟩ ⟨s.scores,k⟩ k
  exact (Nat.add_le_add input (Nat.add_le_add score (Nat.add_le_add_right choose _))).trans
    (arithmetic k N)

theorem perRow_le (k : ℕ) : perRow k ≤ 3200*(k+1)*2^(3*k) := by
  have room : 2^k+1≤2*(2^k) := by have := Nat.two_pow_pos k; omega
  calc
    _ ≤ 400*(k+1)*(2*(2^k))^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left room _)
    _ = 3200*(k+1)*(2^k)^3 := by ring
    _ = _ := by rw [←pow_mul,Nat.mul_comm k 3]

end Hierarchy.DescentGL.RowStageRAM

end OAI
