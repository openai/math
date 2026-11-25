import OAI.LinearAlgebra.SpectralBooks.BorderCircuitTransport
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGrid.IndependentSetGrid
import OAI.LinearAlgebra.SpectralBooks.PlaneCompression
import OAI.LinearAlgebra.SpectralBooks.PlaneSizeGap

/-!
# The circuit contradiction on independent-set grids

The Tree lower bound is on degree-component border circuit size. The network
upper bound is on exact circuits for the same grid polynomial. We use the
actual straight-line program and Zariski-closure definitions to pass between
them, and iterate a single-step table compression to obtain the upper bound.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Filter MvPolynomial

noncomputable section

/-- An exact program bounds the degree-component border size over an infinite
field, in particular over the algebraic closure of its prime field. -/
theorem degreeBorderSize_le_program {F σ : Type*} [Field F] [Infinite F]
    (d : ℕ) {r : ℕ} (p : Program F σ r) (o : Fin r) :
    degreeBorderSize d (registerPolynomial p o) ≤ p.cost := by
  apply (degreeBorderSize_le_iff ..).mpr
  apply (circuitClosure_map_iff (K := F) (L := AlgebraicClosure F) d p.cost _).mpr
  exact zeroLocus_vanishingIdeal_le _ ⟨r, p, o, le_rfl, rfl⟩

/-- The remaining local input to the planar upper bound. The cost function
bounds the scalar network contraction after pinning local entries. A step
computes the next collection of tables, whose entries can be reused. -/
structure GridTableCompression (a : ℕ) where
  cost : ℕ → ℕ → ℝ
  pinConstant : ℝ
  gateConstant : ℝ
  widthConstant : ℝ
  pin_nonneg : 0 ≤ pinConstant
  gate_nonneg : 0 ≤ gateConstant
  width_nonneg : 0 ≤ widthConstant
  finalCost : ∀ w : ℕ, 0 < w → cost 1 w ≤ (2:ℝ)^(gateConstant * (w + Real.log 2))
  step : ∀ n w : ℕ, 1 < n → 0 < w → ∃ w' : ℕ, 0 < w' ∧
    (w':ℝ) ≤ 10*w + widthConstant * Real.log (2*n) ∧
    cost n w ≤ (2:ℝ)^(gateConstant * (w + Real.log (2*n))) + cost (max 1 (n/a)) w'

/-- In the Tree phase, compression of the pinned grids and the stretched
exponential border lower bound on their graph polynomials are incompatible.
The two external inputs are the local table compression with circuits on the
grids, and the border lower bound from the circuit dichotomy. -/
theorem independentSetGrid_contradiction {F : Type*} [Field F] [Infinite F]
    (m k : ℕ → ℕ) (E : (n : ℕ) → Fin (m n) → Fin (k n) → Prop)
    (order : ∀ᶠ n : ℕ in atTop, m n + k n = n)
    (compress : ∀ a : ℕ, 2 ≤ a → ∃ b : GridTableCompression a,
      ∀ᶠ n : ℕ in atTop, ∃ W : ℕ, 0 < W ∧
        (W:ℝ) ≤ b.widthConstant * Real.log (2 * ((m n * k n + 2*n : ℕ):ℝ)) ∧
        ∃ (r : ℕ) (p : Program F ((Fin (m n) ⊕ Fin (k n)) × Bool) r) (o : Fin r),
          registerPolynomial p o = IndependentSetGrid.contraction (E n)
            (fun i s => X (Sum.inl i,s)) (fun _ _ => 1)
            (fun j s => X (Sum.inr j,s)) (fun _ _ => 1) ∧
          (p.cost : ℝ) ≤ (2:ℝ)^(b.pinConstant * Real.log (2 * ((m n * k n + 2*n : ℕ):ℝ))) +
            b.cost (m n * k n + 2*n) W)
    {δ : ℝ} (hδ : 0 < δ)
    (lower : ∀ᶠ n : ℕ in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^δ))
      (IndependentSetGrid.polynomial (R := F) (E n))) : False := by
  let N (n : ℕ) := m n * k n + 2*n
  let size (n : ℕ) := degreeBorderSize n (IndependentSetGrid.polynomial (R := F) (E n))
  apply grid_circuit_size_bounds_incompatible N size size _ (Eventually.of_forall fun _ => le_rfl) _ hδ lower
  · filter_upwards [order, eventually_ge_atTop 1] with n h hn
    exact ⟨by dsimp [N]; positivity, bipartite_grid_size_le h⟩
  · intro a ha
    obtain ⟨b, hgrid⟩ := compress a ha
    let C := 10 / Real.log 2 + b.gateConstant * (20*b.widthConstant + 1)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hC : 0 < C := add_pos_of_pos_of_nonneg (div_pos (by norm_num) hlog)
      (mul_nonneg b.gate_nonneg (by linarith [b.width_nonneg]))
    refine ⟨C + b.pinConstant + (Real.log 2)⁻¹,
      add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hC b.pin_nonneg) (inv_nonneg.mpr hlog.le), ?_⟩
    filter_upwards [hgrid, eventually_ge_atTop 1] with n hg hn
    obtain ⟨W, hWpos, hW, r, p, o, hp, hc⟩ := hg
    rw [IndependentSetGrid.contraction_eq_polynomial] at hp
    have hz : (size n:ℝ) ≤ p.cost := by
      change (degreeBorderSize n _ : ℝ) ≤ p.cost
      rw [← hp]
      exact_mod_cast degreeBorderSize_le_program n p o
    have hN : 1 ≤ N n := by dsimp [N]; omega
    let ℓ := Real.log (2 * N n)
    let P := ((N n : ℝ)^Real.logb a 10) * ℓ
    have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by
      have : (1:ℝ) ≤ N n := by exact_mod_cast hN
      linarith)
    have hP : ℓ ≤ P := le_mul_of_one_le_left (hlog.le.trans hℓ)
      (Real.one_le_rpow (by exact_mod_cast hN) (Real.logb_nonneg (by exact_mod_cast (show 1 < a from ha)) (by norm_num)))
    have ne : 0 ≤ P := (hlog.le.trans hℓ).trans hP
    have hbnd : b.cost (N n) W ≤ (2:ℝ)^(C*P) :=
      planar_size_of_compression_step ha hN hWpos b.gate_nonneg b.width_nonneg b.cost hW b.finalCost b.step
    have hpin : b.pinConstant * ℓ ≤ (C + b.pinConstant)*P := by
      linarith only [mul_le_mul_of_nonneg_left hP b.pin_nonneg, mul_nonneg hC.le ne]
    have htab : C*P ≤ (C+b.pinConstant)*P := by linarith only [mul_nonneg b.pin_nonneg ne]
    have h1 : 1 ≤ (Real.log 2)⁻¹ * P := by
      rw [← div_eq_inv_mul, le_div_iff₀ hlog, one_mul]
      exact hℓ.trans hP
    calc
      (size n : ℝ) ≤ (2:ℝ)^(b.pinConstant*ℓ) + b.cost (N n) W := hz.trans hc
      _ ≤ 2 ^ ((C + b.pinConstant)*P) + 2 ^ ((C + b.pinConstant)*P) := add_le_add
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hpin)
        (hbnd.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) htab))
      _ = 2 ^ ((C + b.pinConstant)*P + 1) := by
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [mul_assoc]
        change _ ≤ (C + b.pinConstant + (Real.log 2)⁻¹)*P
        linarith only [h1]

end

end SpectralBooks
end LinearAlgebra
end OAI
