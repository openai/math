import OAI.Computability.BorderVNP.DiagonalReduction

/-! # Polynomial bit bounds for a common reduction of the whole signed diagonal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing MvPolynomial

universe u v

variable {K : Type v} [Field K] {D m : ℕ} {ι : Type}

/-- The common prime, finite field and scalar entries chosen before any live
or substituted pin in the diagonal program. -/
structure CommonField (G : PaidIdentity K D m) (aux : ι → K) (q k s : ℕ)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) where
  /-- Characteristic of the finite computation. -/
  p : ℕ
  prime : p.Prime
  fixed : q = 0 ∨ p = q
  /-- Finite field containing the common scalar entries. -/
  E₀ : Type
  [field : Field E₀]
  [char_p : CharP E₀ p]
  [finite : Finite E₀]
  /-- Reduction of each fixed shortening and auxiliary table position. -/
  entry : G.Entry ⊕ ι → E₀
  preserves : PreservesTables G aux entry
  closure : NumberedClosure E₀ k s ord

attribute [instance] CommonField.field CommonField.char_p CommonField.finite

/-- One polynomial bounds the prime bit length, and one fixed exponent bounds
the residue field degree, for every length and every small circuit. The fields
in the border hypothesis may vary with the length. -/
theorem commonField_of_borderApprox [Fintype ι] (q : ℕ) [CharP K q]
    (G : PaidIdentity K D m) (aux : ι → K) :
    ∃ B A C : ℕ, ∀ (k s : ℕ) (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
      (F : Type u) [Field F] [CharP F q],
      BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1))) →
        ∃ R : CommonField G aux q k s ord, Nat.card R.E₀ ≤ R.p ^ B ∧
          Nat.clog 2 R.p ≤ A * (2*(k+1)+s+1)^C := by
  rcases CharP.char_is_prime_or_zero K q with hq | rfl
  · let : Fact q.Prime := ⟨hq⟩
    obtain ⟨E, fE, cE, finiteE, y, hy, all⟩ := fixed_prime_tables.{u,v} q G aux
    refine ⟨Nat.card E, Nat.clog 2 q, 0, ?_⟩
    intro k s ord F _ _ hp
    let R : CommonField G aux q k s ord :=
      ⟨q,hq,Or.inr rfl,E,y,hy,all k s ord F hp⟩
    refine ⟨R, ?_, by simp [R]⟩
    exact (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hq.two_le _))
  · let := CharP.charP_to_charZero K
    obtain ⟨e,B,all⟩ := varying_prime_tables.{u,v} G aux
    obtain ⟨A,C,bound⟩ := ParseTable.exists_uniform_tablePrimeExponent_bound
    refine ⟨B,A*(e+1)^C,C,?_⟩
    intro k s ord F _ _
    let := CharP.charP_to_charZero F
    intro hp
    obtain ⟨p,prime,hpSize,E,fE,cE,finiteE,y,hcard,hy,hclosure⟩ := all k s ord F hp
    let R : CommonField G aux 0 k s ord :=
      ⟨p,prime,Or.inl rfl,E,y,hy,hclosure⟩
    refine ⟨R,hcard,?_⟩
    let M := 2*(k+1)+s+e
    have hexp := bound (Fin (2*(k+1))) k s e M (by simp [M]; omega) (by dsimp [M]; omega)
      (by dsimp [M]; omega) (by dsimp [M]; omega)
    change Nat.clog 2 p ≤ _
    calc
      Nat.clog 2 p ≤ ParseTable.tablePrimeExponent (Fin (2*(k+1))) k s e :=
        Nat.clog_le_of_le_pow hpSize
      _ ≤ A * (M+1)^C := hexp
      _ ≤ A * ((e+1)*(2*(k+1)+s+1))^C := by
        gcongr
        dsimp [M]
        nlinarith
      _ = _ := by rw [mul_pow]; ring

/-- The actual shortening over the chosen field. Its local tables read the first
block of the jointly chosen tuple, so later scalar extensions use those same values. -/
noncomputable def CommonField.shortening {G : PaidIdentity K D m} {aux : ι → K} {q k s : ℕ}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} (R : CommonField G aux q k s ord) :
    PaidIdentity R.E₀ D m := reducedIdentity G aux R.entry R.preserves

/-- Specialization leaves each concrete placed network available for the fixed compiler. -/
theorem CommonField.shortening_network {G : PaidIdentity K D m} {aux : ι → K} {q k s : ℕ}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} (R : CommonField G aux q k s ord)
    (a : Fin G.count) : R.shortening.net a = G.net a := rfl

end Diagonal

end BorderVNP
end Computability
end OAI
