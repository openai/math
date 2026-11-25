import OAI.Hierarchy.ProbeScore

namespace OAI
/-! # Explicit penalized inventory prices and the probe purchase account -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

/-- The unrestricted critical point for the two quadratic pieces of the
score, followed by capping at the commodity's physical route length. -/
def critical (a b M s z : ℝ) : ℝ :=
  if z ≤ 2*s*a*M then z/(2*s*a) else (z+2*s*b*M)/(2*s*(a+b))

def offer (a b M s z A : ℝ) := min A (critical a b M s z)

theorem critical_spec {a b M s z : ℝ} (ha : 0<a) (hb : 0≤b) (hM : 0≤M)
    (hs : 0<s) (hz : 0≤z) :
    0 ≤ critical a b M s z ∧ s*rowSlope a b M (critical a b M s z) = z := by
  have A : 0 < 2*s*a := by positivity
  have B : 0 < 2*s*(a+b) := by positivity
  by_cases low : z ≤ 2*s*a*M
  · rw [critical,ite_eq_left low]
    have hr : z/(2*s*a) ≤ M := (div_le_iff₀ A).mpr (by linarith)
    refine ⟨div_nonneg hz A.le, ?_⟩
    rw [rowSlope, rise, max_eq_right (sub_nonpos.mpr hr)]
    field_simp [ha.ne',hs.ne']
   ; ring
  · rw [critical,ite_eq_right low]
    have hr : M ≤ (z+2*s*b*M)/(2*s*(a+b)) :=
      (le_div_iff₀ B).mpr (by nlinarith only [lt_of_not_ge low])
    refine ⟨hM.trans hr, ?_⟩
    rw [rowSlope, rise, max_eq_left (sub_nonneg.mpr hr)]
    field_simp [hs.ne',(add_pos_of_pos_of_nonneg ha hb).ne']
   ; ring

theorem rowSlope_mono {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Monotone (rowSlope a b M) := by
  intro x y xy
  have bound : rise M x ≤ rise M y := max_le_max (sub_le_sub_right xy M) le_rfl
  exact add_le_add (mul_le_mul_of_nonneg_left xy (by positivity))
    (mul_le_mul_of_nonneg_left bound (by positivity))

theorem offer_spec {a b M s z A : ℝ} (ha : 0<a) (hb : 0≤b)
    (hM : 0≤M) (hs : 0<s) (hz : 0≤z) (hA : 0≤A) :
    let x := offer a b M s z A
    x ∈ Set.Icc 0 A ∧ ∀ y ∈ Set.Icc 0 A, (z-s*rowSlope a b M x)*(y-x) ≤ 0 := by
  obtain ⟨hc,der⟩ := critical_spec ha hb hM hs hz
  dsimp only [offer]
  refine ⟨⟨le_min hA hc, min_le_left _ _⟩, ?_⟩
  intro y hy
  rcases le_total A (critical a b M s z) with low|high
  · rw [min_eq_left low]
    apply mul_nonpos_of_nonneg_of_nonpos _ (sub_nonpos.mpr hy.2)
    apply sub_nonneg.mpr
    exact (mul_le_mul_of_nonneg_left (rowSlope_mono ha.le hb low) hs.le).trans_eq der
  · rw [min_eq_right high,der,sub_self,zero_mul]

variable {I : Type*} [Fintype I]

def maximizer (a M s : ℝ) (b A z : I → ℝ) (i : I) :=
  offer a (b i) M s (z i) (A i)

def potential (a M s : ℝ) (b A z : I → ℝ) :=
  let x := maximizer a M s b A z
  pairing z x - s*score a M b x

/-- The actual box optimizer pays a Bregman penalty at every other feasible
offer. Along the reserve feed this is the negative term repaying the probe. -/
theorem potential_gap {a M s : ℝ} (b A z y : I → ℝ) (ha : 0<a)
    (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s) (hz : ∀ i, 0≤z i)
    (hA : ∀ i, 0≤A i) (hy : ∀ i, y i ∈ Set.Icc 0 (A i)) :
    pairing z y - s*score a M b y ≤
      potential a M s b A z - s*divergence a M b (maximizer a M s b A z) y := by
  let x := maximizer a M s b A z
  have support (i : I) : (z i - s*rowSlope a (b i) M (x i))*(y i-x i) ≤ 0 :=
    (offer_spec ha (hb i) hM hs (hz i) (hA i)).2 _ (hy i)
  have row (i : I) :
      z i*y i - s*rowScore a (b i) M (y i) ≤
        (z i*x i - s*rowScore a (b i) M (x i)) - s*rowDivergence a (b i) M (x i) (y i) := by
    dsimp only [rowDivergence]
    nlinarith only [support i]
  have sum := Finset.sum_le_sum (s:=Finset.univ) fun i _ => row i
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at sum
  simpa only [potential, score, pairing, divergence_eq_sum, x] using sum

theorem maximizes {a M s : ℝ} (b A z y : I → ℝ) (ha : 0<a)
    (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s) (hz : ∀ i, 0≤z i)
    (hA : ∀ i, 0≤A i) (hy : ∀ i, y i ∈ Set.Icc 0 (A i)) :
    pairing z y - s*score a M b y ≤ potential a M s b A z := by
  have gap := potential_gap b A z y ha hb hM hs hz hA hy
  have nonneg : 0 ≤ divergence a M b (maximizer a M s b A z) y :=
    (Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg ha.le (sq_nonneg _))
      (mul_nonneg (hb i) (sq_nonneg _))).trans (divergence_lower a M b _ _ hb)
  linarith [mul_nonneg hs.le nonneg]

/-- Halving time and inventory halves the attained potential exactly. -/
theorem potential_half {a M s : ℝ} (b A z : I → ℝ) (ha : 0<a)
    (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s) (hz : ∀ i, 0≤z i)
    (hA : ∀ i, 0≤A i) :
    potential a M (s/2) b A (fun i => z i/2) = potential a M s b A z/2 := by
  let x := maximizer a M s b A z
  let y := maximizer a M (s/2) b A (fun i => z i/2)
  have hs' : 0<s/2 := by positivity
  have hz' (i : I) : 0≤z i/2 := div_nonneg (hz i) (by norm_num)
  have hx (i : I) : x i ∈ Set.Icc 0 (A i) := (offer_spec ha (hb i) hM hs (hz i) (hA i)).1
  have hy (i : I) : y i ∈ Set.Icc 0 (A i) := (offer_spec ha (hb i) hM hs' (hz' i) (hA i)).1
  have pair (t : I → ℝ) : pairing (fun i => z i/2) t = pairing z t/2 := by
    unfold pairing
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have lo := maximizes b A (fun i => z i/2) x ha hb hM hs' hz' hA hx
  have hi := maximizes b A z y ha hb hM hs hz hA hy
  change pairing (fun i => z i/2) x - s/2*score a M b x ≤
    pairing (fun i => z i/2) y - s/2*score a M b y at lo
  change pairing z y-s*score a M b y ≤ pairing z x - s*score a M b x at hi
  change pairing (fun i => z i/2) y - s/2*score a M b y = (pairing z x - s*score a M b x)/2
  rw [pair, pair] at lo
  rw [pair]
  linarith

end
end Hierarchy.AdaptiveProbe

end OAI
