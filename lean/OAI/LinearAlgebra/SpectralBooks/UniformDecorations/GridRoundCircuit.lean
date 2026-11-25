import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.GridUniversalPolynomial
import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinInitial
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGrid.GridPinEdgeless

/-! # Gate and width accounting for the uniform planar compression round -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace UniformDecorations

open Arithmetic Arithmetic.RecursiveBlock MvPolynomial PlanarPatch
open scoped BigOperators Classical NNReal

noncomputable section
variable {F : Type*} [Field F]

/-- The complete uniform table family, with its width and gate count after
edge decorations are packed. The original polynomial is an identity in the
table indeterminates at the old width. -/
theorem build_compression_round {n m w s h A B : ℕ} (hn : 0 < n) (hw : 0 < w)
    (S : Spec (MvPolynomial (Address w) F) s h) (hs : s ≤ 8*w)
    (hh : h ≤ w + A * Nat.clog 2 (2*n))
    (hform : ∀ θ d x, HasFormula (2^(B*(w+1))) (S.tensor θ d x))
    (heq : Zpoly n w = Z m (width s h) S.compiled) :
    let D := 2*A + 16
    let C := 49 + 4*D + A + B
    ∃ w' : ℕ, 0 < w' ∧ w' ≤ 10*w + C*Nat.clog 2 (2*n) ∧
      ∃ p : Family F (Address w) (Address w'),
        p.cost ≤ 2^(C*(w + Nat.clog 2 (2*n))) ∧
        Zpoly n w = bind₁ (familyPolynomial p) (Zpoly m w') := by
  let L := Nat.clog 2 (2*n)
  let D := 2*A+16
  let C := 49+4*D+A+B
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (by omega)
  have hwidth : width s h ≤ 10*w + D*L := by
    rw [width_eq]
    change h ≤ w + A*L at hh
    dsimp [D]
    nlinarith
  obtain ⟨p, hp, hcost⟩ := S.compile_family (W := 2^(B*(w+1))) (Nat.one_le_pow _ _ (by decide)) hform
  refine ⟨width s h, by rw [width_eq]; omega, ?_, p, ?_, ?_⟩
  · have hDC : D ≤ C := by dsimp [C]; omega
    exact hwidth.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hDC) _)
  · have hcard := card_address_le (width s h)
    rw [card_mapType] at hcard
    have hc₁ : 62 ≤ (2:ℕ)^6 := by decide
    have hbit : 2^h+1 ≤ 2^(h+1) := by rw [pow_succ]; have := Nat.two_pow_pos h; omega
    have htotal := Nat.mul_le_mul (hcard.trans (Nat.mul_le_mul_right _ hc₁))
      (Nat.mul_le_mul_right (2^(B*(w+1))) hbit)
    apply hcost.trans (htotal.trans ?_)
    simp only [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    change h ≤ w + A*L at hh
    change _ ≤ C*(w+L)
    dsimp [C]
    nlinarith only [hwidth, hh, Nat.mul_le_mul_left B hL, hL, hw,
      Nat.zero_le (D*w), Nat.zero_le (A*w), Nat.zero_le (49*L)]
  · rw [heq, bind₁_Zpoly]
    apply congrArg (Z m (width s h))
    funext θ x
    exact (hp ⟨θ,x⟩).symm

/-- A compression round for the universal map polynomial at every scale
contradicts the Tree-case border lower bound on bipartite independent sets.
The base case and pinning circuits are included in this specialization. -/
theorem grid_contradiction_of_rounds [Infinite F]
    (rounds : ∀ a : ℕ, 2 ≤ a → ∃ C : ℕ, ∀ n w : ℕ, 1 < n → 0 < w →
      ∃ w' : ℕ, 0 < w' ∧ w' ≤ 10*w + C*Nat.clog 2 (2*n) ∧
      ∃ p : Family F (Address w) (Address w'), p.cost ≤ 2^(C*(w+Nat.clog 2 (2*n))) ∧
        Zpoly n w = bind₁ (familyPolynomial p) (Zpoly (max 1 (n/a)) w'))
    (m k : ℕ → ℕ) (E : ∀ n, Fin (m n) → Fin (k n) → Prop)
    (order : ∀ᶠ n : ℕ in Filter.atTop, m n + k n = n)
    {δ : ℝ} (hδ : 0 < δ)
    (lower : ∀ᶠ n : ℕ in Filter.atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^δ))
      (IndependentSetGrid.polynomial (R := F) (E n))) : False := by
  apply independentSetGrid_contradiction m k E order _ hδ lower
  intro a ha
  obtain ⟨C,hr⟩ := rounds a ha
  let D := max C (max GridPin.pinConstant (Fintype.card (PortGraph.MapClass 1)+4))
  have hCD : C ≤ D := le_max_left ..
  have hpD : GridPin.pinConstant ≤ D := (le_max_left ..).trans (le_max_right ..)
  have hbaseD : Fintype.card (PortGraph.MapClass 1)+4 ≤ D := (le_max_right ..).trans (le_max_right ..)
  let b := gridTableCompressionOfCircuits (Zpoly (F := F)) a D
    (fun w _ => (Zpoly_one_cost (F := F) w).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hbaseD)))
    (fun n w hn hw => by
      obtain ⟨w',hpos,hsize,p,hcost,hpoly⟩ := hr n w hn hw
      exact ⟨w', hpos, hsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hCD) _),
        p, hcost.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hCD)), hpoly⟩)
  refine ⟨b, ?_⟩
  filter_upwards [order, IndependentSetGrid.eventually_positive_classes m k E order hδ lower] with n ho hmk
  let N := m n*k n + 2*n
  have hN : 0 < N := by dsimp [N]; omega
  obtain ⟨W,hW,hs,p,hcost,heq⟩ := GridPin.initialPin (K := F) hmk.1 hmk.2 (E n)
  rw [ho] at hs hcost heq
  have hl : (Nat.clog 2 (2*N) : ℝ) ≤ max 1 (2 / Real.log 2) * Real.log (2*N) :=
    (clog_two_mul_le hN).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.log_nonneg
      (by
        have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
        linarith)))
  have hbit : ((GridPin.pinConstant * Nat.clog 2 (2*N) : ℕ) : ℝ) ≤
      D*max 1 (2 / Real.log 2)*Real.log (2*N) := by
    rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul (by exact_mod_cast hpD) hl (by positivity) (by positivity)
  obtain ⟨r,q,o,hq,hqcost⟩ := exists_program_of_cost (IndependentSetGrid.polynomial (R := F) (E n))
  refine ⟨W,hW,((Nat.cast_le (α := ℝ)).mpr hs).trans hbit,r,q,o,
    hq.trans (IndependentSetGrid.contraction_eq_polynomial (E n)).symm, ?_⟩
  rw [hqcost, heq]
  have h := (Nat.cast_le (α := ℝ)).mpr (polynomialProgramCost_bind_le p (Zpoly N W))
  rw [Nat.cast_add] at h
  apply h.trans (add_le_add_left ?_ _)
  have hp := (Nat.cast_le (α := ℝ)).mpr hcost
  rw [Nat.cast_pow, ← Real.rpow_natCast] at hp
  exact hp.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbit)

end
end UniformDecorations

end SpectralBooks
end LinearAlgebra
end OAI
