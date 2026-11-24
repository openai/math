import OAI.Computability.VPVNP.Classes

/-!
# Closure properties of nonuniform polynomial bounds

The index of a p-projection may revisit small lengths infinitely often. A global
bound by a power of `n + 1` handles those lengths when composing two indices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PolynomiallyBounded

variable {f g : ℕ → ℕ}

/-- An eventual upper estimate by a polynomially bounded function suffices. -/
theorem of_eventually_le (hg : PolynomiallyBounded g) (N : ℕ)
    (h : ∀ n ≥ N, f n ≤ g n) : PolynomiallyBounded f := by
  obtain ⟨A, d, M, hM⟩ := hg
  refine ⟨A, d, max N M, fun n hn => ?_⟩
  exact (h n ((le_max_left ..).trans hn)).trans (hM n ((le_max_right ..).trans hn))

theorem of_le (hg : PolynomiallyBounded g) (h : ∀ n, f n ≤ g n) : PolynomiallyBounded f :=
  hg.of_eventually_le 0 fun n _ => h n

theorem const (c : ℕ) : PolynomiallyBounded (fun _ => c) :=
  ⟨c, 0, 0, fun _ _ => by simp⟩

theorem id : PolynomiallyBounded (fun n => n) :=
  ⟨1, 1, 0, fun _ _ => by simp⟩

theorem add (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨A, a, N, hA⟩ := hf
  obtain ⟨B, b, M, hB⟩ := hg
  refine ⟨A + B, max a b, max 1 (max N M), fun n hn => ?_⟩
  have hn₁ : 1 ≤ n := (le_max_left ..).trans hn
  have hN : N ≤ n := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hM : M ≤ n := (le_max_right ..).trans ((le_max_right ..).trans hn)
  rw [Nat.add_mul]
  apply Nat.add_le_add
  · exact (hA n hN).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn₁ (le_max_left ..)))
  · exact (hB n hM).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn₁ (le_max_right ..)))

theorem mul (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨A, a, N, hA⟩ := hf
  obtain ⟨B, b, M, hB⟩ := hg
  refine ⟨A * B, a + b, max N M, fun n hn => ?_⟩
  calc
    f n * g n ≤ (A * n ^ a) * (B * n ^ b) :=
      Nat.mul_le_mul (hA n ((le_max_left ..).trans hn)) (hB n ((le_max_right ..).trans hn))
    _ = (A * B) * n ^ (a + b) := by rw [pow_add]; ac_rfl

theorem pow (hf : PolynomiallyBounded f) (b : ℕ) :
    PolynomiallyBounded (fun n => f n ^ b) := by
  obtain ⟨A, a, N, hA⟩ := hf
  exact ⟨A ^ b, a * b, N, fun n hn =>
    by simpa only [mul_pow, pow_mul] using Nat.pow_le_pow_left (hA n hn) b⟩

theorem succ : PolynomiallyBounded (fun n => n + 1) := id.add (const 1)

/-- Absorb the finite initial segment of a bounded function into its leading constant. -/
theorem exists_global_bound (hf : PolynomiallyBounded f) :
    ∃ A d : ℕ, ∀ n, f n ≤ A * (n + 1) ^ d := by
  obtain ⟨A, d, N, hA⟩ := hf
  let B := ∑ i ∈ Finset.range N, f i
  refine ⟨A + B, d, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hA n hn).trans (Nat.mul_le_mul (Nat.le_add_right ..)
      (Nat.pow_le_pow_left (Nat.le_succ _) d))
  · have hB : f n ≤ B := Finset.single_le_sum (fun i _ => Nat.zero_le (f i))
      (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    exact hB.trans ((Nat.le_add_left B A).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))))

/-- Composition preserves polynomial bounds even for nonmonotone index functions. -/
theorem comp (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨A, d, hA⟩ := hf.exists_global_bound
  exact ((const A).mul ((hg.add (const 1)).pow d)).of_le (fun n => hA (g n))

end PolynomiallyBounded

end VPVNP
end Computability
end OAI
