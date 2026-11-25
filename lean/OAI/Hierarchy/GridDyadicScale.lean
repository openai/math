import OAI.Hierarchy.GridScaleEnvelope
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.GCongr

namespace OAI
/-! # Dyadic sizes of the grid, controller pins, and selectors

All choices except the padded bank size are common to every tick. Bounds
below at width `w` hold for every actual positive replication factor `q ≤ Q w`. -/

namespace Hierarchy.GridScale
open Filter
noncomputable section

def pins (w a : ℕ) := 2^(w-4*a)
def side (a : ℕ) := 2^(10*a)
def radius (k a : ℕ) := 2^((10*k+16)*a)
def selector (k w a : ℕ) := 2^(w-(10*k+24)*a)
def pairs (A w q : ℕ) : ℕ := (q*2^w) ⌈/⌉ (w^A)
def ticks (k a q : ℕ) := (side a)^k*q
def external (k a B : ℕ) := k*(2*(side a)^(k-1)*B)
def classes (k w : ℕ) := (20*(w+1)+2)^(k+2)

def dyad (x : ℝ) : ℝ := (2:ℝ)^x
theorem dyad_pos (x : ℝ) : 0 < dyad x := Real.rpow_pos_of_pos (by norm_num) _
theorem dyad_mono : Monotone dyad := fun _ _ h =>
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h
theorem dyad_nat (n : ℕ) : ((2^n:ℕ):ℝ) = dyad n := by simp [dyad]
theorem dyad_add (x y : ℝ) : dyad x * dyad y = dyad (x+y) :=
  (Real.rpow_add (by norm_num) _ _).symm
theorem dyad_pow (x : ℝ) (n : ℕ) : (dyad x)^n = dyad (x*n) :=
  (Real.rpow_mul_natCast (by norm_num) x n).symm
theorem dyad_rpow (x y : ℝ) : (dyad x)^y = dyad (x*y) :=
  (Real.rpow_mul (by norm_num) x y).symm

theorem pairs_bounds {w a q : ℕ} (A : ℕ) (ha : a ≤ w) (hw : 0 < w)
    (poly : w^A ≤ 2^a) (hq : 0 < q) (top : q ≤ 2^a) :
    2^(w-a) ≤ pairs A w q ∧ pairs A w q ≤ 2^(w+a) := by
  have den := Nat.pow_pos hw (n:=A)
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := 2^a) _ (Nat.two_pow_pos _)
    calc
      _ = 2^w := by rw [←pow_add, Nat.add_sub_of_le ha]
      _ ≤ q*2^w := Nat.le_mul_of_pos_left _ hq
      _ ≤ w^A*pairs A w q := (ceilDiv_le_iff_le_mul den).mp (le_refl (pairs A w q))
      _ ≤ _ := Nat.mul_le_mul_right _ poly
  · apply (ceilDiv_le_iff_le_mul den).mpr
    calc
      q*2^w ≤ 2^a*2^w := Nat.mul_le_mul_right _ top
      _ = 2^(w+a) := by rw [←pow_add, Nat.add_comm]
      _ ≤ _ := Nat.le_mul_of_pos_left _ den

/-- An arbitrarily small positive fraction of `w` absorbs each fixed multiple of `a(w)`. -/
theorem real_sublinear {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D)
    (C : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ w : ℕ in atTop, (C : ℝ)*(overhead Q D w:ℝ) ≤ ε*w := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((C:ℝ)/ε)
  have coeff := (div_lt_iff₀ he).mp hn
  filter_upwards [sublinear H n] with w small
  have r : (n:ℝ)*(overhead Q D w:ℝ) ≤ (w:ℝ) := by exact_mod_cast small
  have ha := Nat.cast_nonneg (α := ℝ) (overhead Q D w)
  nlinarith only [mul_le_mul_of_nonneg_right coeff.le ha,mul_le_mul_of_nonneg_left r he.le]

/-- The side and radius are subpower, and the chosen pin and selector lengths
are at least `V^(1-ε)`, jointly before the tick is chosen. -/
theorem uniform_sizes {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k : ℕ)
    {ε : ℝ} (he : 0 < ε) : ∀ᶠ w : ℕ in atTop,
    let a := overhead Q D w
    ((side a:ℕ):ℝ) ≤ dyad (ε*w) ∧ ((radius k a:ℕ):ℝ) ≤ dyad (ε*w) ∧
    dyad ((1-ε)*w) ≤ (pins w a:ℝ) ∧ dyad ((1-ε)*w) ≤ (selector k w a:ℝ) := by
  filter_upwards [real_sublinear H 10 he, real_sublinear H (10*k+16) he,
    real_sublinear H 4 he, real_sublinear H (10*k+24) he, sublinear H (10*k+24)] with w hs hr hp hl hfit
  let a := overhead Q D w
  have fit : 4*a ≤ w := le_trans (Nat.mul_le_mul_right a (by omega : 4≤10*k+24)) hfit
  change 4*overhead Q D w ≤ w at fit
  simp only [side,radius,pins,selector,dyad_nat,Nat.cast_sub fit,Nat.cast_sub hfit,
    Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at *
  exact ⟨dyad_mono hs, dyad_mono hr, dyad_mono (by linarith), dyad_mono (by linarith)⟩

/-- Width-`w` allocation error from all geometric resource classes, including
a whole line's `g*q` ticks. The cap is the real three-fifths power of `V`. -/
theorem allocation {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q ≤ Q w →
      (classes k w:ℝ)*((2:ℝ)^w)^(3/5:ℝ)*(side (overhead Q D w)*q:ℕ) ≤ (pairs A w q:ℝ)/16 := by
  filter_upwards [bounds H, sublinear H 100, polynomial H 1 A,
    polynomial H (16*22^(k+2)) (k+2), eventually_ge_atTop 1] with w parameters mature den classesCap hw
  intro q hq top
  let a := overhead Q D w
  have room : a ≤ w := by change 100*a ≤ w at mature; omega
  have divBound : w^A ≤ 2^a := le_trans (Nat.pow_le_pow_left (Nat.le_succ w) A) (by simpa using den)
  have b := (pairs_bounds A room hw divBound hq (top.trans parameters.1)).1
  have cls : 16*classes k w ≤ 2^a := by
    calc
      _ ≤ 16*(22*(w+1))^(k+2) := by
        unfold classes
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (by omega) _
      _ = (16*22^(k+2))*(w+1)^(k+2) := by rw [mul_pow,Nat.mul_assoc]
      _ ≤ _ := classesCap
  have money : (16:ℝ)*(classes k w:ℝ) ≤ dyad a := by rw [←dyad_nat]; exact_mod_cast cls
  have qcap : (q:ℝ) ≤ dyad a := by rw [←dyad_nat]; exact_mod_cast top.trans parameters.1
  have bcap : dyad (w-a:ℕ) ≤ (pairs A w q:ℝ) := by rw [←dyad_nat]; exact_mod_cast b
  have cap : ((2:ℝ)^w)^(3/5:ℝ) = dyad ((w:ℝ)*(3/5:ℝ)) := by
    rw [←Real.rpow_natCast (2:ℝ) w]
    exact dyad_rpow _ _
  have g : (side a:ℝ) = dyad (10*(a:ℝ)) := by
    change ((2^(10*a):ℕ):ℝ) = _
    rw [dyad_nat, Nat.cast_mul, Nat.cast_ofNat]
  have mr : 100*(a:ℝ) ≤ (w:ℝ) := by exact_mod_cast mature
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
  change (classes k w:ℝ)*_*((side a*q:ℕ):ℝ)*16 ≤ _
  rw [Nat.cast_mul,cap,g]
  calc
    _ = (16*(classes k w:ℝ))*dyad ((w:ℝ)*(3/5:ℝ))*(dyad (10*a)*q) := by ring
    _ ≤ dyad a*dyad ((w:ℝ)*(3/5:ℝ))*(dyad (10*a)*dyad a) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right money (dyad_pos _).le)
        (mul_le_mul_of_nonneg_left qcap (dyad_pos _).le)
        (mul_nonneg (dyad_pos _).le (Nat.cast_nonneg _))
        (mul_nonneg (dyad_pos _).le (dyad_pos _).le)
    _ = dyad ((a:ℝ)+w*(3/5:ℝ)+(10*(a:ℝ)+a)) := by
      rw [dyad_add,dyad_add,dyad_add]
    _ ≤ dyad (w-a:ℕ) := by
      apply dyad_mono
      rw [Nat.cast_sub room]
      linarith only [mr, Nat.cast_nonneg (α:=ℝ) w]
    _ ≤ _ := bcap


end
end Hierarchy.GridScale

end OAI
