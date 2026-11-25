import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Choose

/-! # Finite codes for broadcasting a common label -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A code for broadcasting a shared label. Each control point lies on the same
sphere. For a fixed control point the source indices lie on another sphere,
in a hyperplane perpendicular to that control. -/
structure BroadcastCode (m q N : ℕ) where
  H : Fin N ↪ (Fin m → Fin q)
  V : Fin N → Fin N ↪ (Fin m → Fin q)
  H_norm : ∀ x y, (∑ j, (H x j : ℕ) ^ 2) = ∑ j, (H y j : ℕ) ^ 2
  V_norm : ∀ x y z, (∑ j, (V x y j : ℕ) ^ 2) = ∑ j, (V x z j : ℕ) ^ 2
  dot_eq : ∀ x y z, (∑ j, (H x j : ℕ) * (V x y j : ℕ)) =
                      ∑ j, (H x j : ℕ) * (V x z j : ℕ)

namespace BroadcastCode

private theorem exists_constant_embedding {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] {N : ℕ} (f : α → β)
    (h : Fintype.card β * N ≤ Fintype.card α) :
    ∃ e : Fin N ↪ α, ∀ x y, f (e x) = f (e y) := by
  classical
  obtain ⟨v, hv⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f h
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin N) (by simpa using hv)
  have hf (x : Fin N) : f (e x) = v := by
    simpa using he (Set.mem_range_self x)
  exact ⟨e, fun x y => (hf x).trans (hf y).symm⟩

private def dot {m q : ℕ} (a b : Fin m → Fin q) : ℕ :=
  ∑ j, (a j : ℕ) * (b j : ℕ)

private theorem dot_le {m q : ℕ} (a b : Fin m → Fin q) :
    dot a b ≤ m * (q - 1) ^ 2 := by
  have hab (j : Fin m) : (a j : ℕ) * (b j : ℕ) ≤ (q - 1) ^ 2 := by
    have ha := (a j).isLt
    have hb := (b j).isLt
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  calc
    _ ≤ ∑ _j : Fin m, (q - 1) ^ 2 := Finset.sum_le_sum fun j _ => hab j
    _ = _ := by simp

/-- Squared norms and inner products take at most `1 + m * (q-1)^2`
values each. The product bound guarantees enough labels even when both are
prescribed by a common fiber. -/
theorem nonempty_of_card {m q N : ℕ}
    (h : (1 + m * (q - 1) ^ 2) ^ 2 * N ≤ q ^ m) :
    Nonempty (BroadcastCode m q N) := by
  let B := 1 + m * (q - 1) ^ 2
  have hB : 0 < B := by dsimp [B]; omega
  let : NeZero B := ⟨Nat.ne_of_gt hB⟩
  let val (a b : Fin m → Fin q) : Fin B := ⟨dot a b, by
    have := dot_le a b
    dsimp [B]
    omega⟩
  let radius (b : Fin m → Fin q) := val b b
  have h₂ : Fintype.card (Fin B × Fin B) * N ≤ Fintype.card (Fin m → Fin q) := by
    simpa [B, pow_two] using h
  obtain ⟨H, hH⟩ := exists_constant_embedding
    (fun b : Fin m → Fin q => (radius b, radius b)) h₂
  have hV (x : Fin N) := exists_constant_embedding
    (fun b : Fin m → Fin q => (radius b, val (H x) b)) h₂
  choose V hV using hV
  refine ⟨⟨H, V, ?_, ?_, ?_⟩⟩
  · intro x y
    simpa [radius, val, dot, pow_two] using
      congrArg (fun z : Fin B × Fin B => z.1.val) (hH x y)
  · intro x y z
    simpa [radius, val, dot, pow_two] using
      congrArg (fun p : Fin B × Fin B => p.1.val) (hV x y z)
  · intro x y z
    exact congrArg (fun p : Fin B × Fin B => p.2.val) (hV x y z)

end BroadcastCode
end Sunflower
end Combinatorics
end OAI
