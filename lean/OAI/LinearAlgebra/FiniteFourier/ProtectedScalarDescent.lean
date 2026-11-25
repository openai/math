import OAI.LinearAlgebra.FiniteFourier.ProtectedCyclotomicDescent
import OAI.LinearAlgebra.FiniteFourier.ProtectedDescent

/-! # Integral recovery from the ninth- and eighth-root circuits

The ninth-root coefficient algebra has rank six, and the eighth-root algebra
has rank four. Descending both circuits and combining their cleared outputs
gives an integer circuit with a uniform cost bound.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

/-- Recover the integral matrix from its protected cyclotomic circuits.
The odd-prime circuit may depend on the set selected after the ninth-root
circuit is cleared. -/
theorem integralCircuit_of_protectedCyclotomic {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix O I ℤ) {s₃ s₂ : ℕ}
    (atTwo : ∃ k ≤ s₃, ∃ p : Circuit (AdjoinRoot (cyclotomic 9 (protectedRationals {2}))) I O k,
      p.matrix = M.map (Int.castRingHom _))
    (atOdd : ∀ L : Finset ℕ, (∀ p ∈ L, Nat.Prime p) → (∀ p ∈ L, Odd p) →
      ∃ k ≤ s₂, ∃ p : Circuit (AdjoinRoot (cyclotomic 8 (protectedRationals L))) I O k,
        p.matrix = M.map (Int.castRingHom _)) :
    ∃ k ≤ 72 * s₃ + 32 * s₂ + 11 * Fintype.card O, ∃ p : Circuit ℤ I O k, p.matrix = M := by
  have descend (L : Finset ℕ) {d s : ℕ} (hd : 0 < d)
      (h : ∃ k ≤ s, ∃ p : Circuit (AdjoinRoot (cyclotomic d (protectedRationals L))) I O k,
        p.matrix = M.map (Int.castRingHom _)) :
      ∃ k ≤ 2 * d.totient ^ 2 * s + d.totient * Fintype.card O,
        ∃ p : Circuit (protectedRationals L) I O k, p.matrix = M.map (Int.castRingHom _) := by
    obtain ⟨k, hk, p, hp⟩ := h
    obtain ⟨l, hl, q, hq⟩ := circuit_of_protectedCyclotomic L hd M p hp
    exact ⟨l, hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _), q, hq⟩
  obtain ⟨k, hk, p, hp⟩ := integralCircuit_of_protected M (descend {2} (by decide) atTwo)
    (fun L hL hodd => descend L (by decide) (atOdd L hL hodd))
  refine ⟨k, ?_, p, hp⟩
  rw [show (9 : ℕ).totient = 6 by decide, show (8 : ℕ).totient = 4 by decide] at hk
  omega

end FiniteFourier
end LinearAlgebra
end OAI
