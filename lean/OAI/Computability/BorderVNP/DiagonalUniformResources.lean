import OAI.Computability.BorderVNP.DiagonalReaderInputs
import OAI.Computability.BorderVNP.RateCrossing

/-! # Simultaneous asymptotic room for the native reader

The polynomial ceiling is chosen before the ground field, length and circuit.
Every fixed polynomial in this ceiling fits inside one stretched-exponential
batch, including the serialized pin, fixed program, row advice and entry ticks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial VPVNP Filter
open scoped Classical

universe u v

variable {K : Type v} [Field K] {D m : ℕ} {ι : Type} [Fintype ι]

theorem ReaderInputs.mono {G : PaidIdentity K D m} {aux : ι → K} {q k s : ℕ}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField G aux q k s ord}
    {chart : AdvisedBranch R} {teams r bits T U : ℕ}
    (h : ReaderInputs chart teams r bits T) (htu : T ≤ U) : ReaderInputs chart teams r bits U :=
  ⟨h.parameters.trans htu, h.degrees.trans htu, h.monomials.trans htu,
    h.fieldBits.trans htu, h.gates.trans htu, h.labels.trans htu, h.multiplicities.trans htu⟩

/-- A polynomial in the entire Section 9 advice parameter fits below the
batch count with the exact roundings, even when the candidate size varies. -/
theorem polynomial_at_adviceScale_lt_batch {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ)
    {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∀ᶠ n : ℕ in atTop, f (adviceScale σ ρ n) < stretch ρ n := by
  obtain ⟨A,C,bound⟩ := hf.exists_global_bound
  filter_upwards [advice_polynomial_lt_batch hσ hσρ (A*2^C) C, eventually_ge_atTop 1]
    with n hr hn
  let M := adviceScale σ ρ n
  have hM : 1 ≤ M := by dsimp [M,adviceScale]; omega
  calc
    f M ≤ A*(M+1)^C := bound M
    _ ≤ A*(2*M)^C := Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) _)
    _ = A*2^C*M^C := by rw [mul_pow]; ring
    _ < _ := hr

/-- Select one polynomial ceiling that covers the number of physical teams,
the word and tally widths, and all numerical inputs of the actual reader.
These choices precede the field, finite chart and distinguished pin. -/
theorem eventually_reader_inputs (q : ℕ) [CharP K q] (G : PaidIdentity K D m) (aux : ι → K)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ) (physical : ℕ → ℕ) {W e : ℕ}
    (hphysical : ∀ᶠ n : ℕ in atTop, physical n ≤ W*(adviceScale σ ρ n+1)^e) :
    ∃ ceiling : ℕ → ℕ, PolynomiallyBounded ceiling ∧
      (∀ A C : ℕ, ∀ᶠ n : ℕ in atTop, A*(ceiling (adviceScale σ ρ n)+1)^C < stretch ρ n) ∧
      ∀ᶠ n : ℕ in atTop, let T := ceiling (adviceScale σ ρ n)
        physical n ≤ T ∧ ∀ k, k+1 = n → ∀ s ≤ stretch σ n, ∀ teams ≤ physical n,
        ∀ multBits ≤ physical n,
        ∀ (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (F : Type u) [Field F] [CharP F q],
          BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1))) →
          ∃ (R : CommonField G aux q k s ord) (chart : AdvisedBranch R),
            ReaderInputs chart teams (stretch ρ n) multBits T := by
  obtain ⟨A,C,chooseData⟩ := common_reader_inputs.{u,v} q G aux
  let room (M : ℕ) := 3*(M+1) + W*(M+1)^e
  let ceiling (M : ℕ) := A*(room M+1)^C + room M
  have h1 := PolynomiallyBounded.id.add (.const 1)
  have hroom : PolynomiallyBounded room := ((PolynomiallyBounded.const 3).mul h1).add
    ((PolynomiallyBounded.const W).mul (h1.pow e))
  have hc : PolynomiallyBounded ceiling :=
    ((PolynomiallyBounded.const A).mul ((hroom.add (.const 1)).pow C)).add hroom
  refine ⟨ceiling,hc,fun A' C' => polynomial_at_adviceScale_lt_batch hσ hσρ
    ((PolynomiallyBounded.const A').mul ((hc.add (.const 1)).pow C')),?_⟩
  filter_upwards [hphysical] with n hphys
  let M := adviceScale σ ρ n
  have hr : physical n ≤ room M := hphys.trans (Nat.le_add_left _ _)
  have ht : room M ≤ ceiling M := Nat.le_add_left _ _
  refine ⟨hr.trans ht,?_⟩
  intro k hk s hs teams hteams mb hmb ord F _ _ hp
  have hm : 2*(k+1)+s+1 ≤ room M := by dsimp [room,M,adviceScale]; omega
  have hlog : Nat.clog 2 (stretch ρ n+1) ≤ room M := by dsimp [room,M,adviceScale]; omega
  obtain ⟨R,chart,hchart⟩ := chooseData k s teams (stretch ρ n) mb (room M)
    hm (hteams.trans hr) hlog (hmb.trans hr) ord F hp
  exact ⟨R,chart,hchart.mono (Nat.le_add_right _ _)⟩

/-- Ruling out the floored candidate circuit at every sufficiently large
length gives the stretch theorem's real-valued inequality for those lengths. -/
theorem stretch_bound_of_exclusion (F : Type*) [Field F] (σ : ℝ)
    (excluded : ∀ᶠ n : ℕ in atTop,
      ¬ BorderApprox n (stretch σ n) (map (Int.castRingHom F) (Pstar n))) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ)^((n : ℝ)^σ) ≤ borderSize n (map (Int.castRingHom F) (Pstar n)) := by
  filter_upwards [excluded] with n h
  by_contra! hsmall
  exact h (borderSize_le_iff.mp (Nat.le_floor hsmall.le))

end Diagonal

end BorderVNP
end Computability
end OAI
