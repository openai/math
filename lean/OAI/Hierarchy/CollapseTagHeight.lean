import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # Heights available after reserving a polynomial number of groups

Taking the ceiling binary logarithm of the group count ensures that the
whole groups fit. This costs a vanishing fraction of the word length,
including after paying the squared-logarithmic tagged overhead. -/

noncomputable section
namespace Hierarchy.CollapseTagHeight

open Filter Real

def height (A w : ℕ) := w - Nat.clog 2 (w^A)

/-- The ceiling log overshoots the group count by at most one doubling. -/
private theorem pow_clog_le_double (g : ℕ) (hg : 0 < g) : 2^(Nat.clog 2 g) ≤ 2*g := by
  cases hc : Nat.clog 2 g with
  | zero => simpa only [pow_zero] using (show 1 ≤ 2*g by omega)
  | succ c =>
    have hlt : c < Nat.clog 2 g := by omega
    have h := Nat.pow_lt_of_lt_clog hlt
    rw [pow_succ]
    omega

private theorem log_one {w : ℕ} (hw : 1 ≤ w) : 1 ≤ Real.logb 2 (2*(w:ℝ)) := by
  have wr : (1:ℝ) ≤ w := by exact_mod_cast hw
  calc
    (1:ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
    _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)

private theorem loss_sublinear (A : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ w : ℕ in atTop, (Nat.clog 2 (w^A):ℝ) ≤ ε*w := by
  filter_upwards [Tagged.GapScale.eventual_log_sq_le_sqrt ((A:ℝ)+1) he,
    eventually_ge_atTop (1:ℕ)] with w small hw
  have wr : (1:ℝ) ≤ w := by exact_mod_cast hw
  have l := log_one hw
  have logw : Real.logb 2 (w:ℝ) ≤ Real.logb 2 (2*(w:ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have logpos : 0 ≤ Real.logb 2 ((w^A:ℕ):ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.one_le_pow A w hw))
  have ceilBound := Nat.ceil_lt_add_one logpos
  have ceilEq : ⌈Real.logb 2 ((w^A:ℕ):ℝ)⌉₊ = Nat.clog 2 (w^A) := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (w^A)
  rw [ceilEq] at ceilBound
  rw [Nat.cast_pow,Real.logb_pow] at ceilBound
  have sq : Real.logb 2 (2*(w:ℝ)) ≤ (Real.logb 2 (2*(w:ℝ)))^2 := by nlinarith [sq_nonneg (Real.logb 2 (2*(w:ℝ))-1)]
  have scale := mul_le_mul_of_nonneg_left (logw.trans sq) (Nat.cast_nonneg (α:=ℝ) A)
  have sqrt_bound := Real.sqrt_le_self_iff.mpr (Or.inr wr)
  calc
    _ ≤ ((A:ℝ)+1)*(Real.logb 2 (2*(w:ℝ)))^2 := by linarith only [ceilBound,scale,sq,l]
    _ ≤ ε*Real.sqrt w := small
    _ ≤ _ := mul_le_mul_of_nonneg_left sqrt_bound he.le

theorem group_subpower (A : ℕ) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ w : ℕ in atTop, ((w^A : ℕ):ℝ) ≤ (2:ℝ)^(ε*w) := by
  filter_upwards [loss_sublinear A he] with w bound
  calc
    _ ≤ (2:ℝ)^(Nat.clog 2 (w^A)) := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (w^A)
    _ ≤ _ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) bound

theorem width_bounds (A : ℕ) : ∀ᶠ w : ℕ in atTop,
    height A w ≤ w ∧ w ≤ 2*height A w := by
  filter_upwards [loss_sublinear A (by norm_num : (0:ℝ)<1/2)] with w loss
  have double : (2:ℝ)*(Nat.clog 2 (w^A):ℝ) ≤ w := by linarith
  have natDouble : 2*Nat.clog 2 (w^A) ≤ w := by exact_mod_cast double
  dsimp [height]
  omega

theorem tendsto_height (A : ℕ) : Tendsto (height A) atTop atTop := by
  apply tendsto_atTop.2
  intro t
  filter_upwards [width_bounds A,eventually_ge_atTop (2*t)] with w hw hw'
  omega

private theorem reserve_eq {A w : ℕ} (hw : 0 < w) (enough : w ≤ 2*height A w) :
    Nat.clog 2 (w^A) + height A w = w := by
  unfold height at enough ⊢
  omega

theorem volume (A : ℕ) : ∀ᶠ w : ℕ in atTop,
    w^A*2^(height A w) ≤ 2^w ∧ 2^w ≤ 2*(w^A)*2^(height A w) := by
  filter_upwards [width_bounds A,eventually_ge_atTop (1:ℕ)] with w bounds hw
  have sum := reserve_eq hw bounds.2
  have vol : (2:ℕ)^w = 2^(Nat.clog 2 (w^A)) * 2^(height A w) := by rw [← pow_add,sum]
  rw [vol]
  exact ⟨Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _),
    Nat.mul_le_mul_right _ (pow_clog_le_double _ (pow_pos hw _))⟩

/-- A replication budget common to all tag heights up to the current word
length. Taking the floor retains every integral degree bounded by the real cap. -/
def degreeEnvelope (C : ℝ) (w : ℕ) :=
  ⌊(2:ℝ)^(C*(Real.logb 2 (2*(w:ℝ)))^2)⌋₊

theorem degree_le_envelope {C : ℝ} (hC : 0 ≤ C) {h w d : ℕ} (hh : 0 < h)
    (hw : h ≤ w) (hd : Real.logb 2 (d:ℝ) ≤ C*(Real.logb 2 (2*(h:ℝ)))^2) :
    d ≤ degreeEnvelope C w := by
  rcases Nat.eq_zero_or_pos d with rfl | pos
  · exact Nat.zero_le _
  have hpos : (0:ℝ)<h := by exact_mod_cast hh
  have hle : (h:ℝ) ≤ w := by exact_mod_cast hw
  have dpos : (0:ℝ)<d := by exact_mod_cast pos
  have le := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (show 0<2*(h:ℝ) by positivity) (show 2*(h:ℝ) ≤ 2*(w:ℝ) by linarith)
  have both := pow_le_pow_left₀ (zero_le_one.trans (log_one hh)) le 2
  apply Nat.le_floor
  calc
    (d:ℝ) = (2:ℝ)^(Real.logb 2 (d:ℝ)) := (Real.rpow_logb (by norm_num) (by norm_num) dpos).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (hd.trans (mul_le_mul_of_nonneg_left both hC))

theorem degree_subpower (C ε : ℝ) (he : 0 < ε) :
    ∀ᶠ w : ℕ in atTop, (degreeEnvelope C w:ℝ) ≤ (2:ℝ)^(ε*w) := by
  filter_upwards [Tagged.GapScale.eventual_log_sq_le_sqrt C he,eventually_ge_atTop (1:ℕ)]
    with w bound hw
  have wr : (1:ℝ) ≤ w := by exact_mod_cast hw
  exact (Nat.floor_le (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (bound.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr wr)) he.le)))

theorem gap_lower (A : ℕ) (C ε : ℝ) (he : 0 < ε) :
    ∀ᶠ w : ℕ in atTop, (2:ℝ)^((1-ε)*w) ≤ Tagged.gap C (height A w) := by
  have hε := half_pos he
  filter_upwards [loss_sublinear A hε, (tendsto_height A).eventually
    (Tagged.GapScale.eventual_log_sq_le_sqrt C hε), width_bounds A,
    (tendsto_height A).eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with w loss saved bounds hh hw
  have sum := reserve_eq hw bounds.2
  have rs : (Nat.clog 2 (w^A):ℝ) + height A w = w := by exact_mod_cast sum
  have hhR : (1:ℝ) ≤ height A w := by exact_mod_cast hh
  have loR : (height A w:ℝ) ≤ w := by exact_mod_cast bounds.1
  have price := mul_le_mul_of_nonneg_left ((Real.sqrt_le_self_iff.mpr (Or.inr hhR)).trans loR) hε.le
  rw [Tagged.GapScale.gap_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [rs,loss,saved,price])

theorem square_room (A : ℕ) (Q : ℕ → ℕ)
    (hQ : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in atTop, (Q w:ℝ) ≤ (2:ℝ)^(ε*w)) :
    ∀ᶠ w : ℕ in atTop, Q w * 2^w ≤ (2^height A w)^2 := by
  filter_upwards [loss_sublinear A (by norm_num : (0:ℝ)<1/4),
    hQ (1/2) (by norm_num),width_bounds A,eventually_ge_atTop (1:ℕ)] with w loss small bounds hw
  have sum := reserve_eq hw bounds.2
  have rs : (Nat.clog 2 (w^A):ℝ) + height A w = w := by exact_mod_cast sum
  have room : (Q w:ℝ)*(2:ℝ)^w ≤ ((2:ℝ)^(height A w))^2 := by
    calc
      _ ≤ (2:ℝ)^((1/2:ℝ)*w)*(2:ℝ)^w := mul_le_mul_of_nonneg_right small (by positivity)
      _ = (2:ℝ)^((1/2:ℝ)*w+w) := by rw [← Real.rpow_natCast 2 w,Real.rpow_add (by norm_num : (0:ℝ)<2)]
      _ ≤ (2:ℝ)^((height A w:ℝ)+height A w) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [rs,loss])
      _ = _ := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_natCast,pow_two]
  exact_mod_cast room

theorem const_subpower (K : ℕ) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ w : ℕ in atTop, (K:ℝ) ≤ (2:ℝ)^(ε*w) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop ((K:ℝ)/ε)] with w large
  have exponent : (K:ℝ) ≤ ε*w := by
    simpa only [mul_comm] using (div_le_iff₀ he).mp large
  calc
    (K:ℝ) ≤ (2:ℝ)^K := by exact_mod_cast (Nat.lt_two_pow_self (n:=K)).le
    _ ≤ _ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent

/-- A fixed increase in the normalized network size still fits the square
of the tagged address space. -/
theorem square_room_mul_const (A K : ℕ) (Q : ℕ → ℕ)
    (hQ : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in atTop, (Q w:ℝ) ≤ (2:ℝ)^(ε*w)) :
    ∀ᶠ w : ℕ in atTop, K * (Q w * 2^w) ≤ (2^height A w)^2 := by
  have grow : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in atTop,
      ((K * Q w:ℕ):ℝ) ≤ (2:ℝ)^(ε*w) := by
    intro ε he
    filter_upwards [const_subpower K (ε/2) (half_pos he), hQ (ε/2) (half_pos he)] with w hk hq
    rw [Nat.cast_mul]
    calc
      _ ≤ (2:ℝ)^(ε/2*w)*(2:ℝ)^(ε/2*w) := mul_le_mul hk hq (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring
  simpa only [Nat.mul_assoc] using square_room A (fun w => K*Q w) grow


end Hierarchy.CollapseTagHeight

end
end OAI
