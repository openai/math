import OAI.Hierarchy.ProbeLocalFlattening
import OAI.Hierarchy.ProbePurchase

namespace OAI
/-! # Applying the local signed frames to the purchased probes -/

namespace Hierarchy.AdaptiveProbe
open scoped Classical BigOperators
noncomputable section

private theorem signed_dist {k : ℕ} (x y : Coordinates k) (j : Fin k) (side : Bool) :
    Source.sign side*(y j-x j) ≤ dist x y := by
  have chord := PiLp.dist_apply_le x y j
  rw [Real.dist_eq,abs_sub_comm] at chord
  cases side
  · simp only [Source.sign, Bool.false_eq_true, ite_false, neg_one_mul]
    exact (neg_le_abs (y j-x j)).trans chord
  · simp only [Source.sign, ite_true, one_mul]
    exact (le_abs_self (y j-x j)).trans chord

/-- Coordinates at a tile's output and at the next tile's input coincide on the
zero-price sampler joins. Each chain may use its own frame and its own marked sign.
The cost counts every purchased chain, including all exceptional roots. -/
theorem activation_from_frames {G I : Type*} [Fintype G] [Fintype I] {k H : ℕ}
    (slot : G × Fin H ↪ I) (dir : G → Fin k) (side : G → Bool)
    (z : G → ℕ → Coordinates k) (a M s β u δ η fee : ℝ)
    (purchases : ℕ) (b x y : I → ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (s1 : s ≤ 1)
    (hβ : 0 ≤ β) (hb : ∀ i, 0 ≤ b i) (calibrate : 4*δ^2 ≤ u) (resolution : η < δ)
    (long : 1+η < (H:ℝ)*(δ-η)) (weight : ∀ g j, β ≤ b (slot (g,j)))
    (mark : ∀ g j, u ≤ s*(rise M (x (slot (g,j))))^2)
    (read : ∀ g (j : Fin H), |rise M (y (slot (g,j))) -
      max (Source.sign (side g)*(z g (j.val+1) (dir g)-z g j.val (dir g))) 0| ≤ η)
    (bought : ∀ g, |0-max (dist (z g 0) (z g H)-1) 0| ≤ η) :
    (Fintype.card G:ℝ)*(β*u/8)-(purchases:ℝ)*fee ≤
      (s/2)*divergence a M b x y-(purchases:ℝ)*fee := by
  let coord := fun g j => Source.sign (side g)*(z g j (dir g))
  apply purchase_net_gain slot a M s β u δ η fee purchases b x y coord ha hs s1 hβ hb
    calibrate resolution long weight mark
  · intro g j
    simpa only [coord,mul_sub] using read g j
  · intro g
    have h := bought g
    rw [zero_sub,abs_neg,abs_of_nonneg (le_max_right _ _)] at h
    have distBound := (le_max_left (dist (z g 0) (z g H)-1) 0).trans h
    have projection := signed_dist (z g 0) (z g H) (dir g) (side g)
    dsimp [coord]
    linarith only [distBound,projection]

/-- A literal unnormalized cash margin for the reserve replay. All purchased probes
are charged, whether their local test is accurate or exceptional. -/
theorem activation_cash {n bought good : ℕ} {s div reward fee ρ : ℝ}
    (hr : 0 < reward) (hn : 0 < n) (hρ : 0 < ρ) (density : ρ*n ≤ bought)
    (exceptions : (bought:ℝ)-good ≤ ρ*n/4) (unit : fee ≤ reward/2)
    (frames : (good:ℝ)*reward-(bought:ℝ)*fee ≤ (s/2)*div-(bought:ℝ)*fee) :
    0 < (n:ℝ)*ρ*reward/4 ∧ 2*((bought:ℝ)*fee+(n:ℝ)*ρ*reward/4) ≤ s*div := by
  refine ⟨by positivity,?_⟩
  have paid := mul_le_mul_of_nonneg_left unit (Nat.cast_nonneg (α:=ℝ) bought)
  have count := mul_le_mul_of_nonneg_right density hr.le
  have loss := mul_le_mul_of_nonneg_right exceptions hr.le
  nlinarith only [frames,paid,count,loss]

end
end Hierarchy.AdaptiveProbe

end OAI
