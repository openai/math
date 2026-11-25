import OAI.Hierarchy.GridDyadicScale

namespace OAI
/-! # Uniform envelopes for the finite descent iteration -/

noncomputable section
namespace Hierarchy.CollapseOracle
open Filter GridScale
open scoped BigOperators

def Small (q : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in atTop, (q w:ℝ) ≤ dyad (ε*w)

def Near (D : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in atTop, dyad ((1-ε)*w) ≤ D w

theorem small_one : Small (fun _ => 1) := by
  intro ε pos
  exact Filter.Eventually.of_forall (fun w => by
    have := dyad_mono (show 0≤ε*(w:ℝ) by positivity)
    simpa [dyad] using this)

theorem near_volume : Near (fun w => (2:ℝ)^w) := by
  intro ε pos
  exact Filter.Eventually.of_forall (fun w => (dyad_mono
    (show (1-ε)*(w:ℝ)≤w by nlinarith [mul_nonneg pos.le (Nat.cast_nonneg (α:=ℝ) w)])).trans_eq
      (by simp [dyad]))

theorem small_mul {f g : ℕ → ℕ} (hf : Small f) (hg : Small g) :
    Small (fun w => f w*g w) := by
  intro ε pos
  filter_upwards [hf (ε/2) (half_pos pos),hg (ε/2) (half_pos pos)] with w a b
  simp only [Nat.cast_mul]
  refine (mul_le_mul a b (by positivity) (by dsimp [dyad]; positivity)).trans_eq ?_
  rw [dyad_add]; congr 1; ring

theorem small_poly (C A : ℕ) : Small (fun w => C*w^A) := by
  have E : Envelopes (fun _ => 1) (fun w => (2:ℝ)^w) := fun ε hp =>
    (small_one ε hp).and (near_volume ε hp)
  intro ε he
  filter_upwards [polynomial E C A,real_sublinear E 1 he] with w poly exponent
  have a : C*w^A ≤ 2^(overhead (fun _ => 1) (fun j => (2:ℝ)^j) w) :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _)).trans poly
  calc
    _ ≤ _ := by exact_mod_cast a
    _ = _ := dyad_nat _
    _ ≤ _ := dyad_mono (by simpa using exponent)

theorem small_const (C : ℕ) : Small (fun _ => C) := by simpa using small_poly C 0

theorem small_power (A : ℕ) : Small (fun w => w^A) := by simpa using small_poly 1 A

theorem near_min {D D' : ℕ → ℝ} (hf : Near D) (hg : Near D') :
    Near (fun w => min (D w) (D' w)) := by
  intro ε he
  filter_upwards [hf ε he,hg ε he] with w a b
  exact le_min a b

private theorem twice_dyad {a b : ℝ} (less : a<b) :
    ∀ᶠ w : ℕ in atTop, 2*dyad (a*w) ≤ dyad (b*w) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/(b-a))
  filter_upwards [eventually_ge_atTop n] with w hw
  have margin := (div_lt_iff₀ (sub_pos.mpr less)).mp hn
  have wn : (n:ℝ) ≤ w := by exact_mod_cast hw
  have step := mul_le_mul_of_nonneg_right wn (sub_nonneg.mpr less.le)
  calc
    _ = dyad (1+a*w) := by rw [← dyad_add]; norm_num [dyad]
    _ ≤ _ := dyad_mono (by nlinarith only [margin,step])

theorem near_sub {D : ℕ → ℝ} {q : ℕ → ℕ} (large : Near D) (small : Small q) :
    Near (fun w => D w-q w) := by
  intro ε he
  let δ := min (ε/2) (1/4)
  have hd : 0<δ := lt_min (half_pos he) (by norm_num)
  have e : 1-ε < 1-δ := by dsimp [δ]; linarith [min_le_left (ε/2) (1/4:ℝ)]
  have qlt : 1/4 < 1-δ := by dsimp [δ]; linarith [min_le_right (ε/2) (1/4:ℝ)]
  filter_upwards [large δ hd,small (1/4) (by norm_num),twice_dyad e,twice_dyad qlt]
    with w old few a b
  linarith

theorem near_pos {D : ℕ → ℝ} (large : Near D) : ∀ᶠ w : ℕ in atTop, 0<D w := by
  filter_upwards [large 1 (by norm_num)] with w h
  exact (by dsimp [dyad]; positivity : 0<dyad ((1-1)*w)).trans_le h

end Hierarchy.CollapseOracle

end
end OAI
