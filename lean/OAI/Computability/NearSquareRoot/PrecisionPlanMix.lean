import OAI.Computability.NearSquareRoot.PrecisionPlanNode

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication KernelPass PhysicalWalsh PhysicalWalshGrid

/-- A physical fixed-template mix checks its actual row accumulator guards
and propagates the errors of all lanes through the dyadic row sum. -/
theorem mix_numericalStep {a W i o : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W)
    (s : Shape) (hs : 0 < s.level) (frac : ℕ)
    (child : Fin (a+1) → Shape → IdealRow → IdealRow) (c : Fin o → Fin i → Coefficient)
    {cap δ : ℝ} (hδ : 0 ≤ δ) (hcap : cap*2^frac < 2^s.w)
    (hround : Real.sqrt (laneCount a W s) * (2/2^frac) ≤ δ) :
    NumericalStep (nodeOps hW plan) (idealOps a W child) (nodeGuards hW plan) s
      (laneSize a W s) (laneGap a W frac s) (.mix c) ((mixGain c : ℝ)+1) cap δ := by
  intro x y B e hB he head ball
  let n := laneCount a W s
  let v := fun j => atWidth n (y j)
  let select := fun j : Fin n => j.val
  have cover : ∀ z ∈ (coords a W).rows s, ∃ j, select j=z := by
    rw [coords_rows s hs]
    exact fun z hz => ⟨⟨z,List.mem_range.mp hz⟩,rfl⟩
  have hM : 0 ≤ B+e := add_nonneg hB he
  have hm j : ‖decodeRow (coords a W) Shape.w frac s select (x j)‖ ≤ B+e := by
    exact (norm_le_norm_sub_add _ (v j)).trans ((add_le_add (ball j).2 (ball j).1).trans_eq (add_comm ..))
  have hgain : 0 ≤ (mixGain c : ℝ) := Nat.cast_nonneg _
  have room : (mixGain c : ℝ)*(B+e)*2^frac < 2^s.w := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ (by positivity)) hcap
    exact le_trans (by nlinarith : (mixGain c:ℝ)*(B+e) ≤ (mixGain c+1)*(B+e+δ)) head
  constructor
  · exact mixFits_of_rows (coords a W) Shape.w c frac s select cover x (B+e) hM hm room
  · intro b
    have hn := idealMixRow_gain c v B hB (fun j => (ball j).1) b
    have er := mix_row_error (coords a W) Shape.w c frac s select x v (B+e) e hM he hm
      (fun j => (ball j).2) room b
    change laneSize a W s ((idealOps a W child).mix c s y b) ≤ _ ∧ _
    unfold laneSize
    rw [atWidth_idealMix]
    constructor
    · exact hn.trans (by nlinarith)
    · change ‖decodeRow (coords a W) Shape.w frac s select (mix (coords a W) Shape.w c s x b) -
          atWidth (laneCount a W s) ((idealOps a W child).mix c s y b)‖ ≤ _
      rw [atWidth_idealMix]
      rw [Fintype.card_fin] at er
      apply er.trans
      change Real.sqrt (laneCount a W s) * (2 / 2^frac) + (mixGain c : ℝ)*e ≤
        (mixGain c + 1)*(e+δ)
      nlinarith [mul_nonneg hgain hδ]

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
