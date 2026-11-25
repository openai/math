import OAI.Computability.BorderVNP.PackedPotential
import OAI.Computability.BorderVNP.PackedDeliveries

/-!
# Literal capacity for the private site descriptions

In Proposition 7.2 the public directory stores one description for each initial site of each
bottom bundle. The factor counting bottom bundles occurs on both sides of the storage budget.
The positive exponent gap absorbs the fixed index overhead uniformly in the allowed team size.
The floor of the literal width and its integer halving are both included.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Filter TeamScales

/-- The volume and index overhead per processor, before dividing by the initial batch size,
are little-o of the batch size times the number of reserved bits in one processor's literal. -/
theorem eventually_private_tail_room {α τ : ℝ} (hα : 0 < α) (hsmall : α < 1 / 1000)
    (hτ : 0 < τ) (hτsmall : τ < α / 100) (D : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A ε : ℝ, 0 ≤ A → 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) →
        A * (n : ℝ) ^ (1 + τ / 20) * (logWidth r n : ℝ) ^ D ≤
          ε * ((width n α * (literal α n / 2) : ℕ) : ℝ) := by
  obtain ⟨ω, hω, hlog⟩ := exists_polylog_budget D (show 0 < τ / 2000 by positivity)
  refine ⟨ω, hω, fun A ε hA hε ↦ ?_⟩
  have hlit : 0 < 1 - α / 3 := by linarith
  have batch := eventually_le_rounded_width (show α / 2 < α by linarith) hα
    (show (0 : ℝ) < 1 by norm_num) 1
  have data := eventually_le_rounded_width
    (show 1 + τ / 20 + τ / 2000 - α / 2 < 1 - α / 3 by linarith) hlit
    (show 0 < ε / 4 by positivity) A
  have two := eventually_le_rounded_width hlit hlit (show (0 : ℝ) < 1 by norm_num) 2
  filter_upwards [hlog, batch, data, two, eventually_ge_atTop 1] with n hl hb hd ht hn
  simp only [one_mul] at hb
  simp only [Real.rpow_zero, mul_one, one_mul] at ht
  have ht' : 2 ≤ literal α n := by exact_mod_cast ht
  have half : (literal α n : ℝ) ≤ 4 * ((literal α n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show literal α n ≤ 4 * (literal α n / 2) by omega)
  have hp : 0 < (n : ℝ) := by exact_mod_cast hn
  intro r hr hrmax
  calc
    _ ≤ A * (n : ℝ) ^ (1 + τ / 20) * (n : ℝ) ^ (τ / 2000) :=
      mul_le_mul_of_nonneg_left (hl r hr hrmax) (by positivity)
    _ = (n : ℝ) ^ (α / 2) * (A * (n : ℝ) ^ (1 + τ / 20 + τ / 2000 - α / 2)) := by
      rw [mul_assoc, mul_left_comm _ A, ← Real.rpow_add hp, ← Real.rpow_add hp]
      congr 2
      ring
    _ ≤ (width n α : ℝ) * (ε / 4 * literal α n) :=
      mul_le_mul hb hd (by positivity) (by positivity)
    _ ≤ (width n α : ℝ) * (ε / 4 * (4 * ((literal α n / 2 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left half (by positivity)) (by positivity)
    _ = _ := by rw [Nat.cast_mul]; ring

/-- All bottom bundles' site strings fit into the reserved tails of the actual number of
teams in (7.1), using the site-data bound from the volume in (7.2). -/
theorem eventually_private_directory_fits {α τ : ℝ} (hα : 0 < α) (hsmall : α < 1 / 1000)
    (hτ : 0 < τ) (hτsmall : τ < α / 100) (D : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ n : ℕ in atTop,
      ∀ r K V dB : ℕ, 1 ≤ r → (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) →
        ((V * dB : ℕ) : ℝ) ≤ A * volume τ r n * (logWidth r n : ℝ) ^ D →
        K ^ epochs τ n * V * dB ≤ teams α τ K n * r * (literal α n / 2) := by
  obtain ⟨ω, hω, room⟩ := eventually_private_tail_room hα hsmall hτ hτsmall D
  refine ⟨ω, hω, fun A hA ↦ ?_⟩
  filter_upwards [room A 1 hA (by norm_num)] with n hn
  intro r K V dB hr hrmax hsite
  have hcap := hn r hr hrmax
  simp only [one_mul] at hcap
  have hper : V * dB ≤ r * (width n α * (literal α n / 2)) := by
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      _ ≤ (r : ℝ) * (A * (n : ℝ) ^ (1 + τ / 20) * (logWidth r n : ℝ) ^ D) := by
        simpa only [volume, mul_assoc, mul_left_comm] using hsite
      _ ≤ _ := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hcap (by positivity)
  simpa only [teams, mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left (K ^ epochs τ n) hper

/-- Under the computed capacity, the publicly ordered directory recovers one string per
initial site and bottom bundle from the reserved processor tails. -/
theorem deliver_packed_directory {α τ : ℝ} {n K r V dB : ℕ} {Cell : Type*}
    (cell : Fin (K ^ epochs τ n) × Fin V → Cell)
    (fits : K ^ epochs τ n * V * dB ≤ teams α τ K n * r * (literal α n / 2))
    (strings : Fin (K ^ epochs τ n * V) → Fin dB → Bool)
    (key : Fin (K ^ epochs τ n) × Fin V) :
    let capacity : ∑ _j : Fin (K ^ epochs τ n * V), dB ≤
        teams α τ K n * r * (literal α n / 2) := by simpa using fits
    ∃! j, privateDemand cell j = (key, cell key) ∧ ∀ bit : Fin dB,
      storeTails (fun _ ↦ dB) strings (tailAddress (fun _ ↦ dB) capacity ⟨j, bit⟩) = strings j bit :=
  private_delivery_once cell (fun _ ↦ dB) _ strings key

end Packing

end BorderVNP
end Computability
end OAI
