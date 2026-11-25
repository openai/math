import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.GridRoundCircuit

/-! # Planar compression and pinning for every bipartite graph family

A grid with two nonempty vertex classes uses the pinned map polynomial. When a
class is empty its exact product of linear forms satisfies the same gate budget.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace UniformDecorations

open Arithmetic Arithmetic.RecursiveBlock MvPolynomial Filter
open scoped Classical

variable {F : Type*} [Field F]

private theorem grid_pin_cost {m k : ℕ} (E : Fin m → Fin k → Prop) (hsize : 0 < m+k) :
    let N := m*k + 2*(m+k)
    let bits := GridPin.pinConstant * Nat.clog 2 (2*N)
    ∃ W : ℕ, 0 < W ∧ W ≤ bits ∧
      polynomialProgramCost (IndependentSetGrid.polynomial (R := F) E) ≤
        2^bits + polynomialProgramCost (Zpoly (F := F) N W) := by
  let N := m*k + 2*(m+k)
  by_cases h : 0 < m ∧ 0 < k
  · obtain ⟨W,pos,width,p,cost,identity⟩ := GridPin.initialPin (K := F) h.1 h.2 E
    refine ⟨W,pos,width,?_⟩
    rw [identity]
    exact (polynomialProgramCost_bind_le p _).trans (Nat.add_le_add_right cost _)
  · have he (i : Fin m) (j : Fin k) : ¬ E i j :=
      (h ⟨Nat.zero_lt_of_lt i.isLt, Nat.zero_lt_of_lt j.isLt⟩).elim
    have hN : 0 < N := by dsimp [N]; omega
    have hlog : 0 < Nat.clog 2 (2*N) := Nat.clog_pos (by decide) (by omega)
    have hc : 0 < GridPin.pinConstant := by unfold GridPin.pinConstant; omega
    have hbits : Nat.clog 2 (2*N) ≤ GridPin.pinConstant * Nat.clog 2 (2*N) :=
      Nat.le_mul_of_pos_left _ hc
    refine ⟨1,by decide,hlog.trans_le hbits,?_⟩
    apply (IndependentSetGrid.programCost_edgeless (F := F) he).trans
    calc
      2*(m+k) ≤ 2*N := by dsimp [N]; omega
      _ ≤ 2^(Nat.clog 2 (2*N)) := Nat.le_pow_clog (by decide) _
      _ ≤ 2^(GridPin.pinConstant * Nat.clog 2 (2*N)) := Nat.pow_le_pow_right (by decide) hbits
      _ ≤ _ := Nat.le_add_right _ _

/-- A typed compression circuit at every scale supplies the compression and
pinning premise of `independentSetGrid_contradiction` for any graph family. -/
theorem grid_compress_of_rounds
    (rounds : ∀ a : ℕ, 2 ≤ a → ∃ C : ℕ, ∀ n w : ℕ, 1 < n → 0 < w →
      ∃ w' : ℕ, 0 < w' ∧ w' ≤ 10*w + C*Nat.clog 2 (2*n) ∧
      ∃ p : Family F (Address w) (Address w'), p.cost ≤ 2^(C*(w+Nat.clog 2 (2*n))) ∧
        Zpoly n w = bind₁ (familyPolynomial p) (Zpoly (max 1 (n/a)) w'))
    (m k : ℕ → ℕ) (E : ∀ n, Fin (m n) → Fin (k n) → Prop)
    (order : ∀ᶠ n : ℕ in atTop, m n + k n = n) :
    ∀ a : ℕ, 2 ≤ a → ∃ b : GridTableCompression a,
      ∀ᶠ n : ℕ in atTop, ∃ W : ℕ, 0 < W ∧
        (W:ℝ) ≤ b.widthConstant * Real.log (2 * ((m n * k n + 2*n : ℕ):ℝ)) ∧
        ∃ (r : ℕ) (p : Program F ((Fin (m n) ⊕ Fin (k n)) × Bool) r) (o : Fin r),
          registerPolynomial p o = IndependentSetGrid.contraction (E n)
            (fun i s => X (Sum.inl i,s)) (fun _ _ => 1)
            (fun j s => X (Sum.inr j,s)) (fun _ _ => 1) ∧
          (p.cost : ℝ) ≤ (2:ℝ)^(b.pinConstant * Real.log (2 * ((m n * k n + 2*n : ℕ):ℝ))) +
            b.cost (m n * k n + 2*n) W := by
  intro a ha
  obtain ⟨C,hr⟩ := rounds a ha
  let D := max C (max GridPin.pinConstant (Fintype.card (PortGraph.MapClass 1)+4))
  have hCD : C ≤ D := le_max_left ..
  have hpD : GridPin.pinConstant ≤ D := (le_max_left ..).trans (le_max_right ..)
  have hbaseD : Fintype.card (PortGraph.MapClass 1)+4 ≤ D := (le_max_right ..).trans (le_max_right ..)
  let b := gridTableCompressionOfCircuits (Zpoly (F := F)) a D
    (fun w _ => (Zpoly_one_cost (F := F) w).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hbaseD)))
    (fun n w hn hw => by
      obtain ⟨w',hpos,hsize,p,hcost,hpoly⟩ := hr n w hn hw
      exact ⟨w', hpos, hsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hCD) _),
        p, hcost.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hCD)), hpoly⟩)
  refine ⟨b, ?_⟩
  filter_upwards [order,eventually_gt_atTop 0] with n ho hn
  let N := m n*k n + 2*n
  have hN : 0 < N := by dsimp [N]; omega
  obtain ⟨W,hW,hs,hcost⟩ := grid_pin_cost (F := F) (E n) (by omega)
  rw [ho] at hs hcost
  have hl : (Nat.clog 2 (2*N) : ℝ) ≤ max 1 (2 / Real.log 2) * Real.log (2*N) :=
    (clog_two_mul_le hN).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.log_nonneg
      (by have : (1:ℝ) ≤ N := by exact_mod_cast hN
          linarith)))
  have hbit : ((GridPin.pinConstant * Nat.clog 2 (2*N) : ℕ) : ℝ) ≤
      D*max 1 (2 / Real.log 2)*Real.log (2*N) := by
    rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul (by exact_mod_cast hpD) hl (by positivity) (by positivity)
  obtain ⟨r,q,o,hq,hqc⟩ := exists_program_of_cost (IndependentSetGrid.polynomial (R := F) (E n))
  refine ⟨W,hW,((Nat.cast_le (α := ℝ)).mpr hs).trans hbit,r,q,o,
    hq.trans (IndependentSetGrid.contraction_eq_polynomial (E n)).symm, ?_⟩
  rw [hqc]
  have hc := (Nat.cast_le (α := ℝ)).mpr hcost
  rw [Nat.cast_add, Nat.cast_pow, ← Real.rpow_natCast] at hc
  exact hc.trans (add_le_add_left (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hbit) _)

end UniformDecorations

end

end SpectralBooks
end LinearAlgebra
end OAI
