import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShortenWires

/-! # The finite two-center estimate for shifted crossing -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace ShiftedCrossing

open SiteTensor

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Field K]

private def ends (v : E) : Fin 2 → E := ![v,-v]

private def terminals (x y : E) : Site → E := Sum.elim (ends x) (ends y)

private theorem dist_opposite (v : E) : dist v (-v) = 2 * ‖v‖ := by
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ v, norm_smul]
  norm_num

private theorem cost_of_term {dx dy r : ℕ} (P : SpectralPlacementPrices K E)
    (x y z : E) (b : Bool) (W : Fin 2 → Fin dx → Fin dy → Fin r → K) :
    P.price (term b W) (terminals x y) ≤
      2 * (Real.logb 2 dx * ‖x-z‖ + Real.logb 2 dy * ‖(if b then -y else y)-z‖ +
        ‖z‖ * Real.logb 2 r) := by
  let T := term b W
  have hr := P.placed_mono (ends z) (term_group_restricts b W)
  rw [P.placed_diagonal_pair] at hr
  have ht := P.transport T (terminals x y) (ends z ∘ cut b)
  rw [Real.dist_eq, P.group] at ht
  have hu := (abs_le.mp ht).2
  have hd : dist (ends z 0) (ends z 1) = 2 * ‖z‖ := dist_opposite z
  rw [hd] at hr
  have hsum : (∑ i : Site, dist (terminals x y i) ((ends z ∘ cut b) i) *
      Real.logb 2 (Fintype.card (T.Leg i))) =
      2 * (Real.logb 2 dx * ‖x-z‖ + Real.logb 2 dy * ‖(if b then -y else y)-z‖) := by
    have cardX (j : Fin 2) : Fintype.card (T.Leg (.inl j)) = dx := Fintype.card_fin dx
    have cardY (j : Fin 2) : Fintype.card (T.Leg (.inr j)) = dy := Fintype.card_fin dy
    have hd (v w : E) : dist v (-w) = dist (-v) w := by rw [← dist_neg_neg v (-w), neg_neg]
    cases b <;> simp [Fintype.sum_sum_type, Fin.sum_univ_two, terminals, cut, partner, ends,
      cardX, cardY, ← dist_eq_norm, hd y z] <;> ring
  rw [hsum] at hu
  dsimp only [T] at hu
  linarith

/-- The two cut costs bound the original wires up to one placement-dependent
constant. The same constant works for every choice of dimensions and factors. -/
theorem exists_finite_placement_bound (P : SpectralPlacementPrices K E) (x y p m : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ C : ℝ, ∀ {dx dy rp rm : ℕ}, 0 < dx → 0 < dy → Factorization K dx dy rp rm →
    2 * (Real.logb 2 dx + Real.logb 2 dy) ≤
      max (2 * (Real.logb 2 dx * ‖x-p‖ + Real.logb 2 dy * ‖y-p‖ + ‖p‖ * Real.logb 2 rp))
        (2 * (Real.logb 2 dx * ‖x-m‖ + Real.logb 2 dy * ‖-y-m‖ + ‖m‖ * Real.logb 2 rm)) + C := by
  obtain ⟨C, hC⟩ := P.exists_binary_sum_overhead (terminals x y)
  refine ⟨C, ?_⟩
  intro dx dy rp rm hdx hdy F
  let U : (∀ i, Leg dx dy i) → K := (term false F.plus).coeff
  let V : (∀ i, Leg dx dy i) → K := (term true F.minus).coeff
  have hid : (target K dx dy).coeff = U + V := funext F.identity
  have hs := hC U V (hid ▸ target_ne_zero hdx hdy)
  have heq : (⟨Leg dx dy, inferInstance, U + V⟩ :
      Raw Site K) = target K dx dy := by
    exact congrArg (fun f => (⟨Leg dx dy, inferInstance, f⟩ : Raw Site K)) hid.symm
  rw [heq, target_price P _ hdx hdy] at hs
  change dist x (-x) * _ + dist y (-y) * _ ≤
    max (P.price (term false F.plus) _) (P.price (term true F.minus) _) + C at hs
  rw [dist_opposite, dist_opposite, hx, hy, mul_one, ← mul_add] at hs
  exact hs.trans <| add_le_add_left (max_le_max (cost_of_term P x y p false F.plus)
    (cost_of_term P x y m true F.minus)) C

end ShiftedCrossing

end

end SpectralBooks
end LinearAlgebra
end OAI
