import OAI.Optimization.LinearProgramming.Compression.AffineRows

/-! Encoding bounds for evaluation of the rational affine minor representatives. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Specialization at a small rational point controls both reduced numerator and denominator.
The number of minor indices does not enter the bound. -/
theorem affine_evalRat_height {ι κ : Type*} [Fintype κ] (F : AffineFamily ι κ)
    (y : κ → ℚ) (u : ι) (s C Y : ℕ) (hs : Fintype.card κ ≤ s)
    (hc : ∀ j, (F.coefficient u j).num.natAbs ≤ C ∧ (F.coefficient u j).den ≤ C)
    (ho : (F.offset u).num.natAbs ≤ C ∧ (F.offset u).den ≤ C)
    (hy : ∀ j, (y j).num.natAbs ≤ Y ∧ (y j).den ≤ Y) :
    let P := (C + 1) * (Y + 1)
    (F.evalRat y u).num.natAbs ≤ (s + 1) * P ^ (s + 2) ∧
    (F.evalRat y u).den ≤ (s + 1) * P ^ (s + 2) := by
  let P := (C + 1) * (Y + 1)
  have hp : 0 < P := by dsimp [P]; positivity
  have hC : C ≤ P := by dsimp [P]; nlinarith
  have hCY : C*Y ≤ P := by dsimp [P]; nlinarith
  have habs (q : ℚ) {c : ℕ} (h : q.num.natAbs ≤ c) : |q| ≤ (c : ℚ) :=
    (rat_abs_le_num_natAbs q).trans (by exact_mod_cast h)
  obtain ⟨_, hn, hd⟩ := F.evalRat_height y u (fun j ↦ ⟨habs _ (hc j).1, (hc j).2⟩)
    ⟨habs _ ho.1, ho.2⟩ hy
  have hm : Fintype.card κ * (C*Y) + C ≤ (s+1)*P := by
    simpa [add_mul] using Nat.add_le_add (Nat.mul_le_mul hs hCY) hC
  have hk : C * (C*Y)^Fintype.card κ ≤ P^(s+1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul hC ((Nat.pow_le_pow_left hCY _).trans (Nat.pow_le_pow_right hp hs))
  constructor
  · calc
      _ ≤ _ := hn
      _ ≤ ((s+1)*P) * P^(s+1) := Nat.mul_le_mul hm hk
      _ = _ := by change _ = (s+1)*P^(s+2); ring
  · exact hd.trans (hk.trans ((Nat.pow_le_pow_right hp (by omega : s+1 ≤ s+2)).trans
        (Nat.le_mul_of_pos_left _ (by omega))))

end Compression
end LinearProgramming
end Optimization
end OAI
