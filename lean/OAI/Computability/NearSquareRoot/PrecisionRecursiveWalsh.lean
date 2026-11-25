import OAI.Computability.NearSquareRoot.PrecisionNodeRecursion

/-! # Accuracy of the executed recursive Walsh stages at the multiplication grid

A node may contain more than one padded input array. The bound permits up to
`2^(2*k)` entries. The initial transform norm bound is `2^(13*k)` while a
later node may receive norm up to `2^(17*k)`. The depth threshold depends
only on the fixed Walsh template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode
open Filter FixedPoint KernelPass PhysicalWalsh

private theorem paddedFault (k : ℕ) {D : ℝ} (hD : D ≤ (2:ℝ)^k) :
    D*((2:ℝ)^k * (2/2^fractionBits k)) ≤ 1/(2:ℝ)^(68*k) := by
  have he : fractionBits k = 68*k+k+k+1 := by unfold fractionBits; omega
  calc
    _ ≤ (2:ℝ)^k * ((2:ℝ)^k * (2/2^fractionBits k)) := by gcongr
    _ = _ := by rw [he,pow_succ,pow_add,pow_add]; field_simp

private theorem paddedRoom {k : ℕ} {D M : ℝ} (hk : 1 ≤ k) (hD : D ≤ (2:ℝ)^k)
    (hM : 0 ≤ M) (h : M ≤ (2:ℝ)^(17*k)) : D * (M+1) ≤ (2:ℝ)^(20*k) := by
  calc
    _ ≤ (2:ℝ)^k * ((2:ℝ)^(17*k)+1) := by gcongr
    _ ≤ (2:ℝ)^k * ((2:ℝ)^(17*k)*2) := by
      gcongr
      linarith [one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ)) (n := 17*k)]
    _ = (2:ℝ)^(k+17*k+1) := by rw [pow_succ,pow_add]; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

/-- Pointwise numerical certificate at address width `k`. -/
def RunAccurateAt {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W) (k : ℕ) : Prop :=
  ∀ s : Shape, s.w = componentBits k → W^s.level ∣ s.pref →
      2^s.level ≤ k → count (a+1) s ≤ 2^(2*k) → ∀ x : Data s,
      ‖nodeValues (a+1) (fractionBits k) s x‖ ≤ (2:ℝ)^(17*k) →
        Good hW plan s x ∧
          ‖nodeValues (a+1) (fractionBits k) s (run hW plan s x) -
            nodeTarget (a+1) (fractionBits k) s x‖ ≤ 1/(2:ℝ)^(68*k)

theorem run_good_of_allowance {a W k : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W)
    (hp : Correct plan) (hk : 1 ≤ k)
    (allowance : ∀ j, 2^j ≤ k → (recursionFactor plan : ℝ)^(j+1) ≤ 2^k) :
    RunAccurateAt hW plan k := by
  intro s hw hd hdepth hvol x hx
  let δ := (2:ℝ)^k * (2/2^fractionBits k)
  have hD := allowance s.level hdepth
  have err := paddedFault k hD
  have small : (recursionFactor plan:ℝ)^(s.level+1)*δ ≤ 1 :=
    err.trans ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num)))
  have fault : Real.sqrt ((2^(2*k):ℕ):ℝ) * ((2:ℝ)/2^fractionBits k) ≤ δ := by
    dsimp only [δ]
    rw [Nat.cast_pow, Nat.cast_ofNat, Nat.mul_comm 2 k, pow_mul, Real.sqrt_sq (by positivity)]
  have step := run_accurate hW plan hp (2^(2*k)) (fractionBits k) (2^(20*k)) δ
    (by positivity) (by dsimp [δ]; positivity) fault s hd hvol (hw ▸ gridRoom k) small
  obtain ⟨good,close⟩ := step x _ le_rfl (paddedRoom hk hD (norm_nonneg _) hx)
  exact ⟨good,close.trans err⟩

theorem eventually_run_good {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W)
    (hp : Correct plan) : ∀ᶠ k : ℕ in atTop, RunAccurateAt hW plan k := by
  filter_upwards [eventually_depthAllowance (recursionFactor plan), eventually_ge_atTop (1:ℕ)] with k allowance hk
  exact run_good_of_allowance hW plan hp hk allowance

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
