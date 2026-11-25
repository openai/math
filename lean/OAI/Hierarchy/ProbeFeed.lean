import OAI.Hierarchy.ProbePotential

namespace OAI
/-! # Exact integer reserve slices and the finite mesh purchase account -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

def delivered (steps bits j : ℕ) := j*bits/steps
def slice (steps bits j : ℕ) := delivered steps bits (j+1)-delivered steps bits j

theorem delivered_monotone (steps bits : ℕ) : Monotone (delivered steps bits) := by
  intro x y xy
  exact Nat.div_le_div_right (Nat.mul_le_mul_right bits xy)

theorem slice_sum (steps bits : ℕ) (positive : 0 < steps) :
    ∑ j ∈ Finset.range steps, slice steps bits j = bits := by
  have partialSum (k : ℕ) : ∑ j ∈ Finset.range k, slice steps bits j = delivered steps bits k := by
    induction k with
    | zero => simp [delivered]
    | succ k ih =>
      rw [Finset.sum_range_succ,ih,slice]
      exact Nat.add_sub_of_le (delivered_monotone steps bits (Nat.le_succ k))
  simpa [delivered,positive.ne'] using partialSum steps

private theorem floor_error (steps bits j : ℕ) (positive : 0 < steps) :
    0≤(j:ℝ)*bits/steps-delivered steps bits j ∧ (j:ℝ)*bits/steps-delivered steps bits j<1 := by
  have rem := Nat.mod_lt (j*bits) positive
  have div := Nat.mod_add_div (j*bits) steps
  have exact' : (((j*bits)%steps : ℕ):ℝ)+(steps:ℝ)*delivered steps bits j=(j:ℝ)*bits := by
    exact_mod_cast div
  have wr : (0:ℝ) < steps := by exact_mod_cast positive
  have remainder : (j:ℝ)*bits/steps-delivered steps bits j=(((j*bits)%steps : ℕ):ℝ)/steps := by
    apply (eq_div_iff wr.ne').2
    rw [sub_mul,div_mul_cancel₀ _ wr.ne']
    linarith
  rw [remainder]
  exact ⟨div_nonneg (Nat.cast_nonneg _) wr.le,(div_lt_one wr).2 (by exact_mod_cast rem)⟩

/-- The deterministic floor schedule returns every bit, with less than one bit of
pointwise rounding error per coordinate per feed. -/
theorem slice_error (steps bits j : ℕ) (positive : 0 < steps) :
    |(slice steps bits j:ℝ)-(bits:ℝ)/steps|<1 := by
  unfold slice
  rw [Nat.cast_sub (delivered_monotone steps bits (Nat.le_succ j))]
  have a := floor_error steps bits j positive
  have b := floor_error steps bits (j+1) positive
  push_cast at b
  have balanced : (j+1:ℝ)*bits/steps=(j:ℝ)*bits/steps+bits/steps := by ring
  rw [balanced] at b
  rw [abs_lt]
  constructor <;> linarith [a.1,a.2,b.1,b.2]

/-- Starting with the lower integer half never costs more potential than the ideal
half. This also covers every odd bit count on a purchase. -/
theorem split_start {I : Type*} [Fintype I] {a M s : ℝ} (b A : I → ℝ) (bits : I → ℕ)
    (w : ℕ) (hw : 0 < w) (ha : 0 < a) (hb : ∀ i, 0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s)
    (hA : ∀ i, 0 ≤ A i) :
    potential a M (s/2) b A (fun i => ((bits i/2:ℕ):ℝ)/w) ≤
      potential a M s b A (fun i => (bits i:ℝ)/w)/2 := by
  let z := fun i => (bits i:ℝ)/w
  let low := fun i => ((bits i/2:ℕ):ℝ)/w
  let x := maximizer a M (s/2) b A low
  have feasible (i : I) : x i ∈ Set.Icc 0 (A i) :=
    (offer_spec ha (hb i) hM (by positivity : 0 < s/2) (by dsimp [low]; positivity) (hA i)).1
  have co (i : I) : low i ≤ z i/2 := by
    have hi : 2*(bits i/2) ≤ bits i := by omega
    have realHi : 2*((bits i/2:ℕ):ℝ) ≤ bits i := by exact_mod_cast hi
    dsimp [low,z]
    have h := div_le_div_of_nonneg_right realHi (show 0 ≤ (w:ℝ) by positivity)
    linarith only [show 2*((((bits i/2:ℕ):ℝ))/w) ≤ (bits i:ℝ)/w by convert h using 1; ring]
  have pair : pairing low x ≤ pairing (fun i => z i/2) x :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (co i) (feasible i).1
  have opt := maximizes b A (fun i => z i/2) x ha hb hM (by positivity : 0 < s/2)
    (fun i => by dsimp [z]; positivity) hA feasible
  rw [potential_half b A z ha hb hM hs (fun i => by dsimp [z]; positivity) hA] at opt
  change pairing low x-(s/2)*score a M b x ≤ _
  exact (sub_le_sub_right pair _).trans opt

/-- All remaining bits are eventually restored. Every finite feed differs from the
ideal real slope by at most two physical bits, uniformly in the split parity. -/
theorem reserve_slices (steps bits : ℕ) (positive : 0 < steps) :
    let rest := bits-bits/2
    bits/2+(∑ j ∈ Finset.range steps, slice steps rest j)=bits ∧
      ∀ j, |(slice steps rest j:ℝ)-(bits:ℝ)/(2*steps)| ≤ 2 := by
  let rest := bits-bits/2
  have split : bits/2+rest=bits := by dsimp [rest]; omega
  refine ⟨by rw [slice_sum _ _ positive]; exact split,?_⟩
  intro j
  have error := slice_error steps rest j positive
  have lower : (bits:ℝ)/2 ≤ rest := by
    have h : bits ≤ 2*rest := by dsimp [rest]; omega
    exact (div_le_iff₀ (by norm_num)).2 (by exact_mod_cast (mul_comm 2 rest ▸ h))
  have upper : (rest:ℝ) ≤ (bits:ℝ)/2+1 := by
    have h : 2*rest ≤ bits+2 := by dsimp [rest]; omega
    have hr : 2*(rest:ℝ) ≤ bits+2 := by exact_mod_cast h
    linarith
  have hs : 0 < (steps:ℝ) := by exact_mod_cast positive
  have hs1 : (1:ℝ) ≤ steps := by exact_mod_cast positive
  have lo := div_le_div_of_nonneg_right lower hs.le
  have hi := div_le_div_of_nonneg_right upper hs.le
  have inv := (one_div_le_one_div_of_le zero_lt_one hs1)
  have scale : (bits:ℝ)/2/steps=(bits:ℝ)/(2*steps) := by ring
  rw [scale] at lo
  rw [add_div,scale] at hi
  rw [abs_le]
  rw [abs_lt] at error
  constructor <;> linarith

/-- Finite purchase feedback, retaining the original price array throughout the
Bregman comparison. Each term in error accounts for a real mesh or bit-rounding loss. -/
theorem finite_purchase {I : Type*} [Fintype I] {a M s : ℝ} (b A z : I → ℝ)
    (ha : 0 < a) (hb : ∀ i,0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s)
    (hz : ∀ i,0 ≤ z i) (hA : ∀ i,0 ≤ A i)
    (steps : ℕ) (many : 0 < steps) (offer : ℕ → I → ℝ) (value error : ℕ → ℝ)
    (start fee saved : ℝ) (admit : ∀ j < steps, ∀ i, offer j i ∈ Set.Icc 0 (A i))
    (bought : ∀ j < steps, 2*(fee+saved) ≤ s*divergence a M b (maximizer a M s b A z) (offer j))
    (initial : value 0 ≤ start+fee+potential a M (s/2) b A (fun i => z i/2))
    (feed : ∀ j < steps, value (j+1) ≤ value j + s/(2*steps)*
      (pairing z (offer j)/s-score a M b (offer j))+error j)
    (rounding : ∑ j ∈ Finset.range steps, error j ≤ saved/2) :
    value steps ≤ start+potential a M s b A z-saved/2 := by
  let F := potential a M s b A z
  let dt := s/(2*steps)
  let rate := (F-2*(fee+saved))/s
  have npos : (0:ℝ) < steps := by exact_mod_cast many
  have dtpos : 0 ≤ dt := by dsimp [dt]; positivity
  have slope (j : ℕ) (hj : j < steps) : pairing z (offer j)/s-score a M b (offer j) ≤ rate := by
    have g := potential_gap b A z (offer j) ha hb hM hs hz hA (admit j hj)
    apply (le_div_iff₀ hs).2
    rw [sub_mul,div_mul_cancel₀ _ hs.ne']
    dsimp only [F]
    nlinarith only [g,bought j hj]
  have walk (n : ℕ) (hn : n ≤ steps) :
      value n ≤ value 0+n*(dt*rate)+∑ j ∈ Finset.range n, error j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,Nat.cast_succ,add_mul,one_mul]
      have current := ih (by omega)
      have next := feed n (by omega)
      have bounded := mul_le_mul_of_nonneg_left (slope n (by omega)) dtpos
      change _ ≤ value n+dt*_+error n at next
      linarith
  have revenue : (steps:ℝ)*(dt*rate)=(F-2*(fee+saved))/2 := by
    dsimp [dt,rate]
    field_simp [hs.ne',npos.ne']

  have total := walk steps le_rfl
  rw [revenue] at total
  rw [potential_half b A z ha hb hM hs hz hA] at initial
  dsimp only [F] at total
  linarith

end
end Hierarchy.AdaptiveProbe

end OAI
