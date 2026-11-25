import OAI.Computability.NearSquareRoot.InterchangeGram
import OAI.Computability.NearSquareRoot.InterchangeLabelRectangles
import OAI.Computability.NearSquareRoot.InterchangeRank
import OAI.Computability.NearSquareRoot.InterchangeStageCost
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The stage budget for the explicit Hamming rectangle family

All four parameters in the transfer count are the actual quantities of the
constructed family: the size of its label set, its modular rank, the largest
local rectangle incidence, and the dimension of the rational address space.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Filter

/-- Number of incident rectangles at a specified endpoint. -/
noncomputable def endpointIncidence (p k : ℕ) (hp : 0 < p) (z : Bool × Label p (2^k)) : ℕ :=
  Fintype.card {r : HammingRectangleKey p k hp // z.2 ∈ labelsOn z.1 r}

/-- Maximum incidence, counting both source and destination endpoints. -/
noncomputable def labelIncidence (p k : ℕ) (hp : 0 < p) : ℕ :=
  Finset.univ.sup (endpointIncidence p k hp)

theorem le_labelIncidence (p k : ℕ) (hp : 0 < p) (side : Bool) (x : Label p (2^k)) :
    endpointIncidence p k hp (side,x) ≤ labelIncidence p k hp :=
  Finset.le_sup (s := Finset.univ) (f := endpointIncidence p k hp) (Finset.mem_univ (side,x))

private theorem incidence_nat_bound (p k : ℕ) (hp : 0 < p) :
    labelIncidence p k hp ≤ ((2*p-1).choose p)^(p+1) * (2^k)^p * (k+1)^(p^2) := by
  apply Finset.sup_le
  intro z _
  refine (card_hammingRectangle_incident_le hp z.1 z.2).trans ?_
  rw [show p^2 = p*p from pow_two p]
  calc
    _ = ((2*p-1).choose p)^(p+1) * (2^k)^p * k^((p-1)*p) := by
      simp only [mul_pow, pow_succ, pow_mul]
      ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_right p (Nat.sub_le _ _))))

private def incidenceCoefficient (p : ℕ) : ℝ :=
  (((2*p-1).choose p : ℕ) : ℝ)^(p+1) * 2^(p^2)

private theorem incidence_real_bound (p k : ℕ) (hp : 0 < p) :
    (labelIncidence p k hp : ℝ) ≤ incidenceCoefficient p *
      ((2 : ℝ)^k)^p * (1+Real.log ((2 : ℝ)^k))^(p^2) := by
  have hi := Nat.cast_le (α := ℝ).mpr (incidence_nat_bound p k hp)
  push_cast at hi
  refine hi.trans ?_
  have hk : (k : ℝ) + 1 ≤ 2 * (1+Real.log ((2 : ℝ)^k)) := by
    rw [Real.log_pow]
    have hl : (1 : ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) k)]
  calc
    _ ≤ (((2*p-1).choose p : ℕ) : ℝ)^(p+1) * ((2 : ℝ)^k)^p *
          (2*(1+Real.log ((2 : ℝ)^k)))^(p^2) := by gcongr
    _ = _ := by rw [mul_pow]; unfold incidenceCoefficient; ring

/-- The actual family fits the per-stream `m^γ` call budget once the stage
and spectral-defect counts satisfy the simultaneous-repair theorem. -/
theorem eventually_hamming_batch_budget (p : ℕ) [Fact p.Prime] (γ B : ℝ)
    (hγ : 1/2 + (3*p-1) / (p : ℝ)^2 < γ) :
    ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      let q := 2^k
      let N := Fintype.card (Label p q)
      let r := (hammingLabelMatrix p q).rank
      let D := Fintype.card (GramIndex (2*p-1) (Word p q))
      let inc := labelIncidence p k (Fact.out : p.Prime).pos
      (m : ℝ) ≤ ((q : ℕ) : ℝ) ^ (p^2) ∧
      ((q : ℕ) : ℝ) ≤ 2 * (m : ℝ)^((p^2 : ℕ) : ℝ)⁻¹ ∧
      ∀ stages R defect : ℕ, 0 < R →
        (stages : ℝ) ≤ B * Real.sqrt (m * (1+Real.log m)) →
        2 * m^3 * defect ≤ R →
        (stages : ℝ) * (B * R * D * (1+inc) * (N + (m : ℝ)*r)) +
          4*(m : ℝ)*defect*N ≤ (R : ℝ)*N*(m : ℝ)^γ := by
  let h := 2*p-1
  let c := (1+h^(p-1))^(p^2)
  let K := max 1 (max B (max ((2+h : ℕ) : ℝ) (max (incidenceCoefficient p) (c : ℝ))))
  have hK : 1 ≤ K := le_max_left ..
  have hbK : B ≤ K := (le_max_left ..).trans (le_max_right ..)
  have hdK : ((2+h : ℕ) : ℝ) ≤ K :=
    (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have hiK : incidenceCoefficient p ≤ K :=
    (le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrK : (c : ℝ) ≤ K :=
    (le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hp := (Fact.out : p.Prime).pos
  filter_upwards [eventually_interchange_batch_budget_with_power p hp γ K hK hγ] with m hm
  obtain ⟨k, hlow, hupp, hbudget⟩ := hm
  refine ⟨k, ?_⟩
  dsimp only
  refine ⟨by simpa using hlow, by simpa using hupp, ?_⟩
  intro stages R defect hR hst hdef
  let q := 2^k
  let qr := (2:ℝ)^k
  have hQ : 1 ≤ q := Nat.one_le_two_pow
  have hcast : (q : ℝ) = qr := by simp [q,qr]
  let N := Fintype.card (Label p q)
  let r := (hammingLabelMatrix p q).rank
  let D := Fintype.card (GramIndex h (Word p q))
  let inc := labelIncidence p k hp
  have hN : 0 < N := by dsimp [N]; rw [card_label]; positivity
  have hs' : (stages : ℝ) ≤ K * Real.sqrt (m * (1+Real.log m)) := hst.trans (by gcongr)
  have hd : (D : ℝ) ≤ K * qr^h := by
    have h' : D ≤ (2+h) * q^h := by
      dsimp only [D]
      rw [card_gramIndex, card_word, Nat.add_mul]
      gcongr
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega : 0 < q) _)
    calc
      _ ≤ (((2+h : ℕ) : ℝ)) * qr^h  := by rw [← hcast]; exact_mod_cast h'
      _ ≤ _ := by gcongr
  have hi : (inc : ℝ) ≤ K*qr^p*(1+Real.log qr)^(p^2) :=
    (incidence_real_bound p k hp).trans (by
      dsimp [qr]
      gcongr
      exact pow_nonneg (by linarith [Real.log_nonneg (one_le_pow₀ (n := k) (by norm_num : (1 : ℝ) ≤ 2))]) _)
  have hr : qr^(p^2)*r ≤ K*N := by
    have hr' : q^(p^2)*r ≤ c*N := by
      rw [Nat.mul_comm _ r]
      exact hammingLabelMatrix_rank_saving p q (by omega)
    calc
      _ ≤ (c : ℝ)*N  := by rw [← hcast]; exact_mod_cast hr'
      _ ≤ _ := by gcongr
  have huse := hbudget stages D inc r N defect R hN hR hs' hd hi hr hdef
  change (stages : ℝ) * (B*R*D*(1+(inc : ℝ))*((N : ℝ)+(m : ℝ)*r)) + 4*(m : ℝ)*defect*N ≤ _
  apply le_trans _ huse
  gcongr

end Interchange

end NearSquareRoot
end Computability
end OAI
