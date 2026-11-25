import OAI.Optimization.LinearProgramming.PriceGame.LearningPool
import OAI.Optimization.LinearProgramming.PriceGame.Complexity

/-! Effective fixed degrees for the generated expert catalogue in Section 7. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Pool

open States.Mass (depth)

private theorem mul_le_power {B x y k j : ℕ} (hx : x ≤ B^k) (hy : y ≤ B^j) :
    x*y ≤ B^(k+j) := (Nat.mul_le_mul hx hy).trans_eq (pow_add B k j).symm

private theorem pow_le_power {B x k : ℕ} (j : ℕ) (hx : x ≤ B^k) :
    x^j ≤ B^(k*j) := (Nat.pow_le_pow_left hx j).trans_eq (pow_mul B k j).symm

private theorem le_first_power {B x : ℕ} (hx : x ≤ B) : x ≤ B^1 := by simpa using hx

private theorem succ_le_power {B x k : ℕ} (hB : 2 ≤ B) (hx : x ≤ B^k) :
    1+x ≤ B^(k+1) := by
  have hpow : 1 ≤ B^k := Nat.one_le_pow k _ (by omega)
  calc
    1+x ≤ B^k + B^k := Nat.add_le_add hpow hx
    _ = B^k*2 := (mul_two _).symm
    _ ≤ B^k*B := Nat.mul_le_mul_left _ hB
    _ = _ := (pow_succ B k).symm

private theorem const_le_power {B a k : ℕ} (hB : 2 ≤ B) (ha : a ≤ 2^k) : a ≤ B^k :=
  ha.trans (Nat.pow_le_pow_left hB k)

private theorem two_pow_succ_le_power {B : ℕ} (hB : 2 ≤ B) (k : ℕ) :
    1 + 2^k ≤ B^(k+1) :=
  succ_le_power (B := B) (x := 2^k) (k := k) hB (Nat.pow_le_pow_left hB k)

private theorem pool_le_power {B T sk cell : ℕ} (a b f : ℕ)
    (hT : T ≤ B^1) (hsk : sk ≤ B^a) (hcell : cell ≤ B^b) :
    T*(sk*cell^f) ≤ B^(1+(a+b*f)) :=
  mul_le_power hT (mul_le_power hsk (pow_le_power f hcell))

/-- The complete list includes both signs, all depths, all pivots and every ordered tuple
with its repetitions. -/
theorem skeleton_size_power (N B : ℕ) (hN : 0 < N) (hNB : N ≤ B) (hB : 2 ≤ B) :
    (Skeleton.enumerate N).length ≤ B^201 := by
  have hn := le_first_power hNB
  have htwo := le_first_power hB
  have hD : depth N ≤ B^2 := by
    apply le_trans _ (succ_le_power hB hn)
    unfold depth
    have h := Nat.log2_le_self N
    omega
  have hV : 2*N^2 ≤ B^3 := mul_le_power htwo (pow_le_power 2 hn)
  have hP : 1+depth N*(2*N^2) ≤ B^6 := succ_le_power hB (mul_le_power hD hV)
  exact (Skeleton.length_enumerate_le N hN).trans
    (mul_le_power hD (mul_le_power htwo (mul_le_power (pow_le_power 64 hV) hP)))

/-- All raw costs are integral. This accounts for the per-feature shrinkages and all skeletons. -/
def exceptionExponent : ℕ := 225

theorem exception_size_power (N R X : ℕ) (hN : 0 < N) (hNX : N ≤ X)
    (hR : R.size ≤ X) (hX : 2 ≤ X) :
    (Skeleton.enumerate N).length * 66^2 * (1+66*(1+R.size)) ≤ X^exceptionExponent := by
  have h66 : 66 ≤ X^7 := const_le_power hX (by decide)
  have hr : 1+R.size ≤ X^2 := succ_le_power hX (le_first_power hR)
  have hmult : 1+66*(1+R.size) ≤ X^10 := succ_le_power hX (mul_le_power h66 hr)
  exact mul_le_power (mul_le_power (skeleton_size_power N X hN hNX hX) (pow_le_power 2 h66)) hmult

/-- One trial contains at most this many probe-price events. -/
def probeBudget (N : ℕ) : ℕ := Complexity.probes * (2*N)^602

private theorem probeBudget_power (N B : ℕ) (hNB : N ≤ B) (hB : 2 ≤ B) :
    probeBudget N ≤ B^1805 := by
  have hprobes : Complexity.probes ≤ B^601 := by
    unfold Complexity.probes
    rw [Nat.add_comm]
    have h := two_pow_succ_le_power hB 600
    exact h.trans_eq (congrArg (fun q : ℕ => B^q) (show 600+1=601 by rfl))
  have h := mul_le_power hprobes (pow_le_power 602 (mul_le_power (le_first_power hB) (le_first_power hNB)))
  exact h.trans_eq (congrArg (fun q : ℕ => B^q) (show 601+(1+1)*602 = 1805 by rfl))

/-- Joint fixed degree in the dimension/log-cost parameter and the number of trials. -/
def catalogueExponent : ℕ := 1 + (201 + 1821 * 66^2)

theorem catalogue_size_power (N R X T : ℕ) (hN : 0 < N) (hNX : N ≤ X)
    (hX : 2 ≤ X) (hT : 0 < T) (hist : ℕ → List (Probe N))
    (hh : ∀ t < T, (hist t).length ≤ T*probeBudget N) :
    (Catalog.entries (fun t => batch N R (hist t)) T).length ≤ (X*T)^catalogueExponent := by
  let B := X*T
  have hXB : X ≤ B := by
    have := Nat.mul_le_mul_left X (show 1 ≤ T by omega)
    simpa [B] using this
  have hTB : T ≤ B := by
    have := Nat.mul_le_mul_right T (show 1 ≤ X by omega)
    simpa [B] using this
  have hB : 2 ≤ B := hX.trans hXB
  have hNB := hNX.trans hXB
  have ht := le_first_power hTB
  have h4160 : 4160 ≤ B^13 := const_le_power hB (by decide)
  have hhist := mul_le_power ht (probeBudget_power N B hNB hB)
  have hc : 2 * (T*probeBudget N*4160)+1 ≤ B^1821 := by
    rw [Nat.add_comm]
    have h := succ_le_power hB (mul_le_power (le_first_power hB) (mul_le_power hhist h4160))
    exact h.trans_eq (congrArg (fun q : ℕ => B^q) (show (1+(1+1805+13))+1=1821 by rfl))
  exact (catalogue_size N R T _ hist hh).trans
    (pool_le_power (B := B) 201 1821 (66^2) ht (skeleton_size_power N B hN hNB hB) hc)

/-- A single fixed trial exponent `225+1+74=300` suffices for these catalogue bounds. -/
theorem trial_exponent_adequate :
    4 * (13 + 2 * catalogueExponent * (exceptionExponent + 1 + 74 + 1)) < 2^74 := by
  norm_num [catalogueExponent, exceptionExponent]

/-- The raw cost bit-width used in `X` is exactly the least binary exponent bounding `R+1`. -/
theorem cost_width_le_iff (R k : ℕ) : R.size ≤ k ↔ R+1 ≤ 2^k := Nat.size_le

end Pool
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
