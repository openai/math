import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecord

/-! # Header bits and gates for the patch replacement catalogue -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace PortGraph


/-- Encode the actual dependent family of record/list-position/role triples.
The factor for the list position contributes exactly one copy of the old
width to each endpoint's header. -/
theorem card_replacement_roles {R : Type*} [Fintype R] {n w tokens c b : ℕ}
    (hn : 0 < n) (hr : Fintype.card R ≤ (2*n)^tokens)
    (L : R → ℕ) (hL : ∀ r, L r ≤ 2^(w+c))
    (roles : (j : (r : R) × Fin (L r)) → Type*) [∀ j, Fintype (roles j)]
    (hroles : ∀ j, Fintype.card (roles j) ≤ b) :
    Fintype.card ((j : (r : R) × Fin (L r)) × roles j) ≤
      2^(w + (tokens+c+b)*Nat.clog 2 (2*n)) := by
  let ℓ := Nat.clog 2 (2*n)
  have hℓ : 1 ≤ ℓ := Nat.clog_pos (by decide) (by omega)
  have hr' : Fintype.card R ≤ 2^(tokens*ℓ) :=
    hr.trans (by
      rw [mul_comm tokens, pow_mul]
      exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)
  have hJ : Fintype.card ((r : R) × Fin (L r)) ≤ Fintype.card R * 2^(w+c) := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _r : R, 2^(w+c) := Finset.sum_le_sum fun r _ => by simpa using hL r
      _ = _ := by simp
  calc
    _ = ∑ j, Fintype.card (roles j) := Fintype.card_sigma
    _ ≤ ∑ _j : (r : R) × Fin (L r), b := Finset.sum_le_sum fun j _ => hroles j
    _ = Fintype.card ((r : R) × Fin (L r)) * b := by simp
    _ ≤ (2^(tokens*ℓ) * 2^(w+c)) * 2^b :=
      Nat.mul_le_mul (hJ.trans (Nat.mul_le_mul_right _ hr')) Nat.lt_two_pow_self.le
    _ ≤ _ := by
      simp only [← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      change tokens * ℓ + (w+c) + b ≤ w+(tokens+c+b)*ℓ
      nlinarith only [Nat.mul_le_mul_left c hℓ, Nat.mul_le_mul_left b hℓ]

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
