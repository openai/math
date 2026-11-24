import OAI.Computability.VPVNP.Classes
import OAI.Computability.VPVNP.Pinning
import OAI.Computability.VPVNP.CycleQuery
import OAI.Computability.VPVNP.QueryPrefix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Projecting the universal integer family onto directed Hamiltonian cycles

For each matrix order, a deterministic finite query program traverses the
directed cycle, checking one full row at a time. Compiling this program with
a budget of `m * m` queries gives a literal machine table. Pinning its prefix
in equation (1.1) leaves exactly the cycle monomials. This construction uses
an order-dependent prefix whose bit length is polynomially bounded.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u

private theorem cycleIndex_bound (A m : ℕ) :
    A * ((m * m + 1) * (2 + m * (m * (m * (m + 1)))) * (m * m + 1) + 1) ^ 2 + m * m ≤
      (16 * A + 1) * (m + 1) ^ 16 := by
  let z := m + 1
  have h₂ : m * m + 1 ≤ z ^ 2 := by dsimp [z]; nlinarith
  have h₄ : 2 + m * (m * (m * (m + 1))) ≤ 3 * z ^ 4 := by
    dsimp [z]; ring_nf; omega
  have h₈ : (m * m + 1) * (2 + m * (m * (m * (m + 1)))) * (m * m + 1) + 1 ≤
      4 * z ^ 8 := by
    have h₁ : 1 ≤ z ^ 8 := Nat.one_le_pow _ _ (by dsimp [z]; omega)
    calc _ ≤ z ^ 2 * (3 * z ^ 4) * z ^ 2 + z ^ 8 :=
           Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul h₂ h₄) h₂) h₁
         _ = _ := by ring
  have h₁₆ : m * m ≤ z ^ 16 := (Nat.le_add_right _ 1).trans <| h₂.trans <|
    Nat.pow_le_pow_right (by dsimp [z]; omega) (by decide)
  calc
    _ ≤ A * (4 * z ^ 8) ^ 2 + z ^ 16 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₈ _)) h₁₆
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.add_mul, one_mul, ← mul_assoc, Nat.mul_comm A]
      rfl

private theorem P_zero : P 0 = 0 := by
  have malformed (x : Fin 0 → Bool) : acceptingCount x = 0 := by
    apply acceptingCount_of_malformed
    simp only [List.ofFn_zero]
    rfl
  simp [P, pairedPolynomial, malformed]

private theorem hamiltonianCyclePolynomial_zero (S : Type*) [CommSemiring S] :
    hamiltonianCyclePolynomial S 0 = 0 := by
  classical
  simp [hamiltonianCyclePolynomial, spanningCycles]

/-- A single polynomially bounded choice of source orders works over all commutative rings. -/
theorem hamiltonian_projection_orders :
    ∃ r : ℕ → ℕ, (∀ m, r m ≤ 16001 * (m + 1) ^ 16) ∧
      ∀ m (R : Type u) [CommRing R], ∃ φ : Projection R (Fin (r m) × Bool) (Fin m × Fin m),
        φ.hom (MvPolynomial.map (Int.castRingHom R) (P (r m))) = hamiltonianCyclePolynomial R m := by
  classical
  have atOrder (m : ℕ) : ∃ n : ℕ, n ≤ 16001 * (m + 1) ^ 16 ∧
      ∀ (R : Type u) [CommRing R], ∃ φ : Projection R (Fin n × Bool) (Fin m × Fin m),
        φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) = hamiltonianCyclePolynomial R m := by
    by_cases hz : m = 0
    · subst m
      refine ⟨0, Nat.zero_le _, ?_⟩
      intro R _
      exact ⟨fun i => Fin.elim0 i.1, by simp [P_zero, hamiltonianCyclePolynomial_zero]⟩
    let root : Fin m := ⟨0, Nat.pos_of_ne_zero hz⟩
    obtain ⟨l, bits, hlen, hcount⟩ := QueryMachine.exists_prefix (cycleQuery root) (m * m)
    refine ⟨l + m * m, ?_, ?_⟩
    · have hcard : Fintype.card (CycleState m) = 2 + m * (m * (m * (m + 1))) := by
        simp [CycleState]
      rw [hcard] at hlen
      exact (Nat.add_le_add_right hlen _).trans (cycleIndex_bound 1000 m)
    · intro R _
      refine ⟨pinVariables bits finProdFinEquiv.symm, P_pin_hamiltonian bits m ?_ R⟩
      intro x
      rw [hcount, cycleIndicator]
      by_cases h : x ∈ (spanningCycles m).image permutationEdges
      · simp [h, (cycleQuery_eval_iff root x).mpr h]
      · have hn := mt (cycleQuery_eval_iff root x).mp h
        simp [h, Bool.eq_false_iff.mpr hn]
  choose r hr hφ using atOrder
  exact ⟨r, hr, hφ⟩

/-- Directed Hamiltonian cycles are p-projections of the integer family over each field. -/
theorem hamiltonian_PProjects (F : Type u) [Field F] :
    PProjects (hamiltonianCyclePolynomial F)
      (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) := by
  obtain ⟨r, hr, hφ⟩ := hamiltonian_projection_orders.{u}
  refine ⟨r, ⟨16001 * 2 ^ 16, 16, 1, ?_⟩, fun m => hφ m F⟩
  intro m hm
  calc
    r m ≤ 16001 * (m + 1) ^ 16 := hr m
    _ ≤ 16001 * (2 * m) ^ 16 := by gcongr; omega
    _ = _ := by rw [mul_pow, mul_assoc]

end VPVNP
end Computability
end OAI
