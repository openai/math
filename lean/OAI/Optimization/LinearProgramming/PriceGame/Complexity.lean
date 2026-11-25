import OAI.Optimization.LinearProgramming.PriceGame.StatesMass
import OAI.Optimization.LinearProgramming.PriceGame.MomentLocalCost
import OAI.Optimization.LinearProgramming.PriceGame.MomentScoreBound
import Mathlib.Data.Nat.Size

/-! Concrete bounds for the trial tree and arithmetic in Sections 5 and 7. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Complexity

open States.Mass (depth)

def probes : ℕ := 2 ^ 600 + 1

/-- Count every call, including the root and all leaf calls. -/
def nodeCount (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | l + 1 => 1 + b * nodeCount b l

theorem nodeCount_le (b l : ℕ) : nodeCount b l ≤ (b + 1) ^ l := by
  induction l with
  | zero => simp [nodeCount]
  | succ l ih =>
    have hpow : 1 ≤ (b + 1) ^ l := Nat.one_le_pow l (b + 1) (by omega)
    calc
      nodeCount b (l+1) = 1 + b * nodeCount b l := rfl
      _ ≤ (b + 1) ^ l + b * (b + 1) ^ l := Nat.add_le_add hpow (Nat.mul_le_mul_left _ ih)
      _ = (b+1) ^ (l+1) := by rw [pow_succ]; ring

theorem const_pow_depth_le (n b k : ℕ) (hn : 0 < n) (hb : b ≤ 2 ^ k) :
    b ^ depth n ≤ (2 * n) ^ k := by
  have hd : 2 ^ depth n ≤ 2 * n := by
    rw [depth, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.log2_self_le hn.ne')
  calc
    b ^ depth n ≤ (2 ^ k) ^ depth n := Nat.pow_le_pow_left hb _
    _ = (2 ^ depth n) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k]
    _ ≤ (2 * n) ^ k := Nat.pow_le_pow_left hd _

private theorem branching_pow_le (k : ℕ) (hk : 1 ≤ k) :
    2*(2^k+1)+1 ≤ (2:ℕ)^(k+2) := by
  have h : 2 ≤ (2:ℕ)^k := by
    calc
      2 = (2:ℕ)^1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hk
  rw [show k+2 = (k+1)+1 from rfl, pow_succ 2 (k+1), pow_succ 2 k]
  omega

theorem trial_nodes_le (n : ℕ) (hn : 0 < n) :
    nodeCount (2 * probes) (depth n) ≤ (2 * n) ^ 602 := by
  unfold probes
  have hb := branching_pow_le 600 (by omega)
  have he : (2:ℕ)^(600+2) = 2^602 :=
    congrArg (fun k : ℕ => 2^k) (show (600:ℕ)+2 = 602 by rfl)
  exact (nodeCount_le _ _).trans
    (const_pow_depth_le n _ 602 hn (hb.trans_eq he))

/-- Calls in an actual adaptive trial, including early leaves. -/
def calls {E : Type*} {r : ℕ} : Moment.Trial E r → ℕ
  | .leaf => 1
  | .node _ _ children => 1 + ∑ j, calls (children j)

private theorem nodeCount_pos (b d : ℕ) : 1 ≤ nodeCount b d := by
  cases d <;> simp [nodeCount]

theorem calls_le_nodeCount {E : Type*} {r : ℕ} (tr : Moment.Trial E r)
    (d : ℕ) (hh : tr.height ≤ d) : calls tr ≤ nodeCount (2*r) d := by
  induction tr generalizing d with
  | leaf => exact nodeCount_pos _ _
  | node mask gain children ih =>
    cases d with
    | zero => simp [Moment.Trial.height] at hh
    | succ d =>
      have hs : (Finset.univ.sup fun j => (children j).height) ≤ d := by
        simpa [Moment.Trial.height] using hh
      change 1 + (∑ j, calls (children j)) ≤ 1 + 2*r * nodeCount (2*r) d
      apply Nat.add_le_add_left
      calc
        _ ≤ ∑ _ : Fin (2*r), nodeCount (2*r) d := Finset.sum_le_sum fun i hi =>
          ih i d ((Finset.le_sup (f := fun j => (children j).height) hi).trans hs)
        _ = _ := by simp

theorem trial_calls_polynomial {E : Type*} (n : ℕ) (hn : 0 < n)
    (tr : Moment.Trial E probes) (hh : tr.height ≤ depth n) : calls tr ≤ (2*n)^602 :=
  (calls_le_nodeCount tr _ hh).trans (trial_nodes_le n hn)

/-- Every nonleaf makes `r` probes, querying at most the number of its coordinates
when computing feedback. Each such designated-label procedure uses one root query. -/
theorem trial_label_calls_le (n : ℕ) (hn : 0 < n) :
    nodeCount (2 * probes) (depth n) * probes * (2*n^2) ≤
      (2*n)^602 * probes * (2*n^2) :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (trial_nodes_le n hn))

/-- Bound for the largest baseline on the first `d` levels. -/
def priceMax (R G : ℕ) : ℕ → ℕ
  | 0 => R + 1
  | d+1 => 2 * G * (2*(R+1) + priceMax R G d)

theorem priceMax_le (R G d : ℕ) :
    priceMax R G d ≤ (R+1) * (8*G+1)^d := by
  induction d with
  | zero => simp [priceMax]
  | succ d ih =>
    have hp : 1 ≤ (8*G+1)^d := Nat.one_le_pow d _ (by omega)
    have hR : R+1 ≤ (R+1) * (8*G+1)^d := by simpa using Nat.mul_le_mul_left (R+1) hp
    calc
      priceMax R G (d+1) ≤ 2*G*(2*((R+1)*(8*G+1)^d) + (R+1)*(8*G+1)^d) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hR) ih)
      _ ≤ (R+1) * (8*G+1)^(d+1) := by rw [pow_succ]; nlinarith only [Nat.zero_le ((R+1)*(8*G+1)^d), Nat.zero_le (G*((R+1)*(8*G+1)^d))]

/-- Binary logarithm bound, including the common denominator `Q` for prices. -/
theorem price_numerator_lt (Q R G d : ℕ) :
    Q * priceMax R G d <
      2 ^ (Q.log2+1 + ((R+1).log2+1) + d*((8*G+1).log2+1)) := by
  have hQ := Nat.lt_log2_self (n := Q)
  have hR := Nat.lt_log2_self (n := R+1)
  have hG := Nat.lt_log2_self (n := 8*G+1)
  calc
    Q * priceMax R G d ≤ (Q*(R+1)) * (8*G+1)^d := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (priceMax_le ..)
    _ < (2^(Q.log2+1)*2^((R+1).log2+1)) * (2^((8*G+1).log2+1))^d := by
      apply lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hQ (by omega)) (by positivity))
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left _ hR.le
      · exact Nat.pow_le_pow_left hG.le _
    _ = _ := by rw [← pow_add, ← pow_mul, ← pow_add, Nat.mul_comm d]

/-- Bounds every earlier baseline, so the next market can refer to any ancestor. -/
theorem price_along_path (R G : ℕ) (hG : 0 < G) (v : ℕ → ℚ)
    (hstart : |v 0| ≤ R+1)
    (hmarket : ∀ k U : ℕ, (∀ j ≤ k, |v j| ≤ U) →
      |v (k+1)| ≤ (2*G : ℚ) * (2*(R+1) + U)) :
    ∀ k j : ℕ, j ≤ k → |v j| ≤ priceMax R G k := by
  intro k
  induction k with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    simpa [this, priceMax] using hstart
  | succ k ih =>
    intro j hj
    rcases (Nat.le_succ_iff_eq_or_le.mp hj) with rfl | hle
    · simpa [priceMax] using hmarket k _ ih
    · apply (ih j hle).trans
      exact_mod_cast (show priceMax R G k ≤ priceMax R G (k+1) from by
        simp only [priceMax]
        have hx := Nat.mul_le_mul_right (2*(R+1)+priceMax R G k) (show 1 ≤ 2*G by omega)
        rw [one_mul] at hx
        omega)

theorem price_numerator_size (R G Q : ℕ) (hG : 0 < G) (hQ : 0 < Q) (v : ℕ → ℚ)
    (hstart : |v 0| ≤ R+1)
    (hmarket : ∀ k U : ℕ, (∀ j ≤ k, |v j| ≤ U) →
      |v (k+1)| ≤ (2*G : ℚ) * (2*(R+1) + U))
    (hden : ∀ j, (v j).den ∣ Q) (d : ℕ) :
    (v d).num.natAbs.size ≤ Q.log2+1 + ((R+1).log2+1) + d*((8*G+1).log2+1) := by
  apply Nat.size_le.mpr
  have hnum := Moment.rat_num_abs_le_of_den_dvd (v d) _ Q hQ
    (price_along_path R G hG v hstart hmarket d d le_rfl) (hden d)
  rw [Nat.mul_comm] at hnum
  exact hnum.trans_lt (price_numerator_lt Q R G d)

private theorem integerFraction_den (a : ℤ) (b : ℕ) :
    ((a:ℚ)/(b:ℚ)).den ∣ b := by
  have hz := Rat.den_dvd a (b:ℤ)
  have hn : (Rat.divInt a (b:ℤ)).den ∣ b := by exact_mod_cast hz
  simpa only [Rat.divInt_eq_div, Int.cast_natCast] using hn

/-- After sharing a fraction 1/64, the entire new set of weights has common
denominator 64 times the new list size times the previous common denominator. -/
theorem fixed_share_den_dvd (m Q : ℕ) (wt total : ℚ)
    (hw : wt.den ∣ Q) (ht : total.den ∣ Q) :
    ((1-1/64:ℚ) * wt + (1 / (64*(m:ℚ))) * total).den ∣ (64*m)*Q := by
  apply (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd ?_ ?_)
  · apply (Rat.mul_den_dvd _ _).trans
    have hden : (1 - 1/64 : ℚ).den ∣ 64 := by
      rw [show (1 - 1/64 : ℚ) = 63/64 by norm_num]
      exact integerFraction_den 63 64
    exact (Nat.mul_dvd_mul hden hw).trans ⟨m, by ring⟩
  · apply (Rat.mul_den_dvd _ _).trans
    have hden : (1/(64*(m:ℚ)) : ℚ).den ∣ 64*m := by
      simpa only [Int.cast_one, Nat.cast_mul, Nat.cast_ofNat] using integerFraction_den 1 (64*m)
    exact Nat.mul_dvd_mul hden ht

/-- The recurrence counts the denominator supplied to the next trial, even when the
individual reduced rational would have a smaller denominator. -/
def shareDen (Q : ℕ) (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => Q
  | t+1 => (64*m t) * shareDen Q m t

theorem shareDen_bound (Q M : ℕ) (m : ℕ → ℕ) (T : ℕ) (hm : ∀ t < T, m t ≤ M) :
    shareDen Q m T ≤ Q*(64*M)^T := by
  induction T with
  | zero => simp [shareDen]
  | succ t ih =>
    have h₀ := hm t (Nat.lt_succ_self _)
    have h₁ := ih (fun j hj => hm j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ (64*M) * (Q*(64*M)^t) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 64 h₀) h₁
      _ = _ := by rw [pow_succ]; ring

theorem shareDen_size (Q M : ℕ) (m : ℕ → ℕ) (T : ℕ) (hm : ∀ t < T, m t ≤ M) :
    (shareDen Q m T).size ≤ Q.size + T*(64*M).size := by
  apply Nat.size_le.mpr
  refine (shareDen_bound Q M m T hm).trans_lt ?_
  have hQ := Nat.lt_size_self Q
  have hM := Nat.lt_size_self (64*M)
  calc
    Q*(64*M)^T ≤ Q * (2^(64*M).size)^T :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM.le _)
    _ < (2^Q.size) * (2^(64*M).size)^T := Nat.mul_lt_mul_of_pos_right hQ (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm T]

end Complexity
end PriceGame
end LinearProgramming
end Optimization
end OAI
