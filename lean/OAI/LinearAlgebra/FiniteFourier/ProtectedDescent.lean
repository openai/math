import OAI.LinearAlgebra.FiniteFourier.ProtectedCircuit
import OAI.LinearAlgebra.FiniteFourier.CircuitRingCombine

/-! # Recovering a tensor circuit over the integers

Clearing a circuit over the rationals localized at two produces an odd scalar
multiple of the desired matrix. A second circuit can protect precisely the
prime factors of that multiplier, so Bézout combination recovers the original
integer matrix, with one extra binary gate per output.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {I O : Type*} [Fintype O] {s : ℕ}

/-- A linear circuit over the protected rationals gives an integral circuit of
identical size for one allowed positive multiple of its integer target. -/
theorem Circuit.clearProtectedMatrix {L : Finset ℕ} (M : Matrix O I ℤ)
    (p : Circuit (protectedRationals L) I O s)
    (hp : p.matrix = M.map (Int.castRingHom (protectedRationals L))) :
    ∃ (D : ℕ) (q : Circuit ℤ I O s), 0 < D ∧ D ∈ denominatorsAvoiding L ∧
      ∀ o i, q.matrix o i = (D : ℤ) * M o i := by
  classical
  let u := p.mapCoeff (protectedRationals L).subtype
  let S := denominatorsAvoiding L
  obtain ⟨q, T, hT, hq⟩ := u.clearDenominators S p.denominatorsIn_protectedRationals
    (fun _ => 1) (fun _ => ⟨Nat.one_pos, S.one_mem⟩)
  simp only [Nat.cast_one, div_one] at hq
  obtain ⟨hD, h⟩ := q.alignOutputs_spec T S _ hT hq
  refine ⟨_, q.alignOutputs T, hD.1, hD.2, fun o i => ?_⟩
  have he : (fun j => (((Pi.single i (1 : ℤ) : I → ℤ) j) : ℚ)) = Pi.single i (1 : ℚ) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  have hm : u.matrix = M.map (Int.castRingHom ℚ) := by
    rw [Circuit.matrix_mapCoeff, hp]
    rfl
  apply Int.cast_injective (α := ℚ)
  rw [Circuit.matrix_apply, h, he, ← Circuit.matrix_apply, hm]
  simp

/-- Uniformly bounded circuits at the prime two and at all prescribed sets of
odd primes give an integer circuit. The bound at odd primes is independent of
the set selected after clearing the first circuit. -/
theorem integralCircuit_of_protected (M : Matrix O I ℤ) {s₀ s₁ : ℕ}
    (atTwo : ∃ k ≤ s₀, ∃ p : Circuit (protectedRationals {2}) I O k,
      p.matrix = M.map (Int.castRingHom _))
    (atOdd : ∀ L : Finset ℕ, (∀ p ∈ L, Nat.Prime p) → (∀ p ∈ L, Odd p) →
      ∃ k ≤ s₁, ∃ p : Circuit (protectedRationals L) I O k,
        p.matrix = M.map (Int.castRingHom _)) :
    ∃ k ≤ s₀ + s₁ + Fintype.card O, ∃ p : Circuit ℤ I O k, p.matrix = M := by
  classical
  obtain ⟨k₀, hk₀, p, hp⟩ := atTwo
  obtain ⟨D, a, hD, htwo, ha⟩ := p.clearProtectedMatrix M hp
  have hodd := odd_of_mem_denominatorsAvoiding_two htwo
  have hpr (l) (hl : l ∈ D.primeFactors) : Nat.Prime l := Nat.prime_of_mem_primeFactors hl
  have hoddFactors (l) (hl : l ∈ D.primeFactors) : Odd l := by
    apply (hpr l hl).odd_of_ne_two
    rintro rfl
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hodd.coprime_two_left)
      (Nat.dvd_of_mem_primeFactors hl)
  obtain ⟨k₁, hk₁, q, hq⟩ := atOdd D.primeFactors hpr hoddFactors
  obtain ⟨E, b, _, hE, hb⟩ := q.clearProtectedMatrix M hq
  have hc : Nat.Coprime D E := by
    apply Nat.coprime_of_dvd
    intro l hl hlD
    exact hl.coprime_iff_not_dvd.mp (hE l (hl.mem_primeFactors hlD hD.ne'))
  obtain ⟨k, hk, z, hz⟩ := circuit_sumPair I O (D.gcdA E) (D.gcdB E) a b
  refine ⟨k, by omega, z, ?_⟩
  ext o i
  rw [Circuit.matrix_apply, hz, ← Circuit.matrix_apply, ← Circuit.matrix_apply, ha, hb]
  have hbez := Nat.gcd_eq_gcd_ab D E
  rw [hc.gcd_eq_one, Nat.cast_one] at hbez
  linear_combination -(M o i) * hbez

end FiniteFourier
end LinearAlgebra
end OAI
