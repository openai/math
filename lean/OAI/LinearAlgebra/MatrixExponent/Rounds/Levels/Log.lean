import OAI.LinearAlgebra.MatrixExponent.Rounds.Scale
import OAI.LinearAlgebra.MatrixExponent.Rounds.Sweep

/-!
# Sizes that can be absorbed by the grouping parameter

When the gain exponent is positive the number of rounds tends to
infinity. The stack depth and reserved block height grow at most
quadratically in this number, uniformly over suitable levels.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Filter

variable {δ : ℝ} {p : Design δ} {M n T₀ : ℕ} {a b ξ : ℝ} (v : Levels p M)

def box (c : ℕ) := 2 ^ (c * (v.j + 1))
def span := 100 + v.stack + p.growth * v.j + v.blocks + v.height

theorem box_mono {s t : ℕ} (h : s ≤ t) : v.box s ≤ v.box t :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)

theorem box_add (s t : ℕ) : v.box (s + t) = v.box s * v.box t := by
  simp only [box, add_mul, pow_add]

theorem box_mul (s t : ℕ) : v.box (s * t) = v.box s ^ t := by
  unfold box
  rw [mul_right_comm, pow_mul]

theorem le_box (s : ℕ) : s ≤ v.box s :=
  Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (by omega)))

theorem group_eq : 2 ^ v.group = v.box p.groupRate := rfl

variable {v}

theorem Suits.box_le (hs : v.Suits n T₀ a b ξ) (c : ℕ) (ha : 4 * a * c ≤ 1) :
    v.box c ≤ Nat.clog 2 n := by
  obtain ⟨hj, hh, _, _, _, _, _, _, ht, _⟩ := hs
  let h : ℝ := Nat.clog 2 n
  have hD : (1 : ℝ) ≤ p.D := by exact_mod_cast (show 1 ≤ p.D by have := p.large; omega)
  have hx : (2 : ℝ) ^ v.j ≤ h ^ (2 * a) :=
    (pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left _ p.gain_pos)).trans
      ((le_mul_of_one_le_left (by positivity) hD).trans ht)
  have he : c * (v.j + 1) ≤ v.j * (2 * c) := by
    calc
      _ ≤ c * (2 * v.j) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have ht' : (2 : ℝ) ^ (c * (v.j + 1)) ≤ h := calc
    _ ≤ (2 ^ v.j : ℝ) ^ (2 * c) := by rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) he
    _ ≤ (h ^ (2 * a)) ^ (2 * c) := pow_le_pow_left₀ (by positivity) hx _
    _ = h ^ (4 * a * c) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ h)]; push_cast; ring_nf
    _ ≤ h := (Real.rpow_le_rpow_of_exponent_le hh.le ha).trans_eq (Real.rpow_one _)
  unfold h at ht'
  unfold box
  exact_mod_cast ht'

theorem eventually_rounds (p : Design δ) (M : ℕ) (ha : 0 < a) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p M) (T₀ : ℕ) (b ξ : ℝ), v.Suits n T₀ a b ξ → j ≤ v.j := by
  filter_upwards [((tendsto_rpow_atTop ha).comp Shaving.tendsto_height).eventually_ge_atTop
    ((2 : ℝ) ^ (p.gain * j))] with n hn v T₀ b ξ hs
  obtain ⟨_, _, _, _, _, _, _, hx, _⟩ := hs
  have he := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hn.trans hx)
  exact Nat.le_of_mul_le_mul_left he p.gain_pos

private theorem Suits.linear (hs : v.Suits n T₀ a b ξ) (hb : b ≤ 1)
    {k : ℕ} (hak : 1 ≤ a * k) : v.stack ≤ 1 + p.gain * v.j * k ∧ v.height ≤ 1 + p.gain * v.j * k := by
  obtain ⟨_, hh, _, he, _, ht, _, hg, _⟩ := hs
  let h : ℝ := Nat.clog 2 n
  have hx : h ≤ (2 : ℝ) ^ (p.gain * v.j * k) := calc
    h ≤ h ^ (a * k) := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hh.le hak
    _ = (h ^ a) ^ k := by rw [Real.rpow_mul (by linarith : 0 ≤ h), Real.rpow_natCast]
    _ ≤ ((2 : ℝ) ^ (p.gain * v.j)) ^ k := pow_le_pow_left₀ (by positivity) hg _
    _ = _ := (pow_mul ..).symm
  have hp : 2 * h ≤ (2 : ℝ) ^ (1 + p.gain * v.j * k) := by rw [pow_add, pow_one]; gcongr
  have hq : h ^ b ≤ h := (Real.rpow_le_rpow_of_exponent_le hh.le hb).trans_eq (Real.rpow_one _)
  have ht' := ht.trans ((mul_le_mul_of_nonneg_left hq (by norm_num)).trans hp)
  exact ⟨(pow_le_pow_iff_right₀ (by norm_num)).mp ht', (pow_le_pow_iff_right₀ (by norm_num)).mp (he.trans hp)⟩

theorem Suits.span_square (hs : v.Suits n T₀ a b ξ) (hb : b ≤ 1)
    {k : ℕ} (hak : 1 ≤ a * k) :
    v.span ≤ (100 + 2 * (1 + p.gain * k) + p.growth + M * (1 + p.gain * k) + 2 * p.steps * p.groupRate) * v.j ^ 2 := by
  let c := 1 + p.gain * k
  have hv := hs.1
  have h₂ : v.j ≤ v.j ^ 2 := Nat.le_self_pow (by decide) _
  have h₁ : 1 ≤ v.j ^ 2 := hv.trans_le h₂
  obtain ⟨ht, hh⟩ := hs.linear hb hak
  have he : 1 + p.gain * v.j * k ≤ c * v.j ^ 2 := by
    rw [show p.gain * v.j * k = p.gain * k * v.j by ring, show c = 1 + p.gain * k from rfl, add_mul, one_mul]
    exact Nat.add_le_add h₁ (Nat.mul_le_mul_left _ h₂)
  have hg : p.steps * v.j * v.group ≤ p.steps * p.groupRate * 2 * v.j ^ 2 := by
    unfold group
    calc
      _ ≤ p.steps * v.j * (p.groupRate * (2 * v.j)) := by gcongr; omega
      _ = _ := by ring
  unfold span blocks remaining
  calc
    _ ≤ 100 * v.j ^ 2 + c * v.j ^ 2 + p.growth * v.j ^ 2 + (M * (c * v.j ^ 2) + p.steps * p.groupRate * 2 * v.j ^ 2) + c * v.j ^ 2 := by
      have hstack := ht.trans he
      have hheight := hh.trans he
      have hcst : 100 ≤ 100 * v.j ^ 2 := Nat.le_mul_of_pos_right _ h₁
      gcongr
    _ = _ := by unfold c; ring

theorem eventually_span (p : Design δ) (M : ℕ) (ha : 0 < a) (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p M) (T₀ : ℕ) (b ξ : ℝ), b ≤ 1 →
      v.Suits n T₀ a b ξ → A * v.span ≤ 2 ^ v.j := by
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / a)
  have hak : 1 ≤ a * k := by rw [mul_comm]; exact (div_le_iff₀ ha).mp hk
  let c := 1 + p.gain * k
  let f := A * (100 + 2 * c + p.growth + M * c + 2 * p.steps * p.groupRate)
  have he : ∀ᶠ j : ℕ in atTop, f * j ^ 2 ≤ 2 ^ j := by
    have hx := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2
      (by norm_num : (1 : ℝ) < 2)).const_mul_left (f : ℝ)
    filter_upwards [hx.eventuallyLE] with j hj
    have he : (f : ℝ) * (j : ℝ) ^ 2 ≤ (2 : ℝ) ^ j := (le_abs_self _).trans (by simpa using hj)
    exact_mod_cast he
  obtain ⟨j, hj⟩ := eventually_atTop.mp he
  filter_upwards [eventually_rounds p M ha j] with n hn v T₀ b ξ hb hs
  refine le_trans ?_ (hj _ (hn v T₀ b ξ hs))
  unfold f
  rw [mul_assoc]
  exact Nat.mul_le_mul_left A (hs.span_square hb hak)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # Grouping slack and the address space at intermediate rounds -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Filter

variable {δ : ℝ} {p : Design δ} {M : ℕ} (v : Levels p M)

def width (i : ℕ) := p.width (2 ^ v.stack) i
def budget (m i : ℕ) := p.budget (8 * (v.allocation m : ℝ) * 2 ^ v.stack) i

theorem width_eq (i : ℕ) : v.width i = 2 ^ (v.stack + p.growth * i) := by
  simp only [width, Design.width, pow_add, mul_comm]

theorem budget_zero (m : ℕ) : v.budget m 0 = 256 * (m : ℝ) * v.batch * (v.stack + 1) := by
  simp only [budget, Design.budget, allocation, batch, mul_zero, pow_zero, div_one, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_add]
  ring

theorem budget_final (m : ℕ) : v.budget m v.j = 8 * v.finalBudget m := by
  unfold budget Design.budget finalBudget
  ring

theorem rounds_le_group : v.j ≤ v.group := by
  have := p.overhead_large
  exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by unfold Design.groupRate; omega))

theorem overhead_le_group : p.overhead ≤ v.group :=
  (Nat.le_add_right ..).trans (Nat.le_mul_of_pos_right _ (by omega))

structure Fits (n A C : ℕ) : Prop where
  positive : 0 < v.j
  span : (A + 4) * v.span ≤ 2 ^ v.j
  group : 2 ^ v.group ≤ Nat.clog 2 n
  small : v.box C ≤ Nat.clog 2 n
  height : Nat.clog 2 n ≤ 2 ^ v.height

theorem eventually_fits (p : Design δ) (M A C : ℕ) {a : ℝ} (ha : 0 < a)
    (hsize : 4 * a * (p.groupRate + C : ℕ) ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p M) (T₀ : ℕ) (b ξ : ℝ), b ≤ 1 →
      v.Suits n T₀ a b ξ → v.Fits n A C := by
  filter_upwards [eventually_span p M ha (A + 4)] with n hn v T₀ b ξ hb hv
  have h := hv.box_le _ hsize
  refine ⟨hv.1, hn v T₀ b ξ hb hv, (v.box_mono (Nat.le_add_right ..)).trans h,
    (v.box_mono (Nat.le_add_left ..)).trans h, ?_⟩
  exact_mod_cast hv.2.2.1

variable {v} {n A C m i : ℕ} (h : v.Fits n A C)

include h in
theorem Fits.four_span : 4 * v.span ≤ 2 ^ v.group :=
  ((Nat.mul_le_mul_right _ (Nat.le_add_left 4 A)).trans h.span).trans
    (Nat.pow_le_pow_right (by decide) v.rounds_le_group)

include h in
theorem Fits.alphabet {t : ℕ} (ht : t ≤ (Nat.clog 2 n) ^ A) : Nat.clog 2 t ≤ 2 ^ v.group := by
  have hx : Nat.clog 2 t ≤ v.height * A := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    rw [pow_mul]
    exact ht.trans (Nat.pow_le_pow_left h.height _)
  have hh : v.height ≤ v.span := Nat.le_add_left ..
  rw [mul_comm] at hx
  exact ((hx.trans (Nat.mul_le_mul (Nat.le_add_right ..) hh)).trans h.span).trans
    (Nat.pow_le_pow_right (by decide) v.rounds_le_group)

include h in
theorem Fits.one_le_budget (hm : n ≤ m) (hi : i ≤ v.j) : 1 ≤ v.budget m i := by
  have hk : p.gain * i ≤ v.group :=
    Nat.mul_le_mul (by unfold Design.groupRate; omega) (hi.trans (Nat.le_succ _))
  have hn : Nat.clog 2 n ≤ n := (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le
  have hb : m ≤ v.allocation m := by
    unfold allocation
    exact ((Nat.le_mul_of_pos_left _ (by decide : 0 < 32)).trans
      (Nat.le_mul_of_pos_right _ (by omega))).trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hx : 2 ^ (p.gain * i) ≤ v.allocation m :=
    (((Nat.pow_le_pow_right (by decide) hk).trans h.group).trans hn).trans (hm.trans hb)
  rw [budget, Design.budget, le_div_iff₀ (by positivity), one_mul]
  exact le_trans (by exact_mod_cast hx : (2 : ℝ) ^ (p.gain * i) ≤ v.allocation m)
    ((le_mul_of_one_le_left (by positivity) (by norm_num)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))))

theorem slack (hi : i ≤ v.j) {N : ℕ} (hN : N ≤ p.overhead ^ (i + 1) * v.allocation m) :
    (N : ℝ) * (v.width i : ℝ) ≤ v.budget m i * (2 : ℝ) ^ v.group := by
  have hh : p.overhead ^ (i + 1) * 2 ^ ((p.gain + p.growth) * i) ≤ 2 ^ v.group := by
    refine le_trans ?_ v.room
    have := p.overhead_large
    gcongr
  have he : N * v.width i * 2 ^ (p.gain * i) ≤ 8 * v.allocation m * 2 ^ v.stack * 2 ^ v.group := calc
    _ ≤ (p.overhead ^ (i + 1) * v.allocation m) * v.width i * 2 ^ (p.gain * i) := by gcongr
    _ = v.allocation m * 2 ^ v.stack * (p.overhead ^ (i + 1) * 2 ^ ((p.gain + p.growth) * i)) := by
      rw [width_eq, add_mul, pow_add 2, pow_add 2]
      ring
    _ ≤ _ := by gcongr; exact Nat.le_mul_of_pos_left _ (by decide)
  rw [budget, Design.budget, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact_mod_cast he

include h in
theorem Fits.address (hm : m ≤ n ^ 2) (hi : i ≤ v.j) {w : ℕ}
    (hw : 2 ^ w ≤ p.overhead ^ (i + 1) * v.allocation m) : w ≤ 4 * Nat.clog 2 n := by
  let l := Nat.clog 2 n
  have hm' : m ≤ 2 ^ (l * 2) := by rw [pow_mul]; exact hm.trans (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) n) _)
  have ho : p.overhead ^ (i + 1) ≤ 2 ^ v.group := by
    refine le_trans ?_ ((Nat.le_mul_of_pos_right _ (by positivity)).trans v.room)
    exact Nat.pow_le_pow_right (by have := p.overhead_large; omega) (Nat.succ_le_succ hi)
  have hv : 5 + v.stack + v.blocks ≤ l := by
    have hx : 4 * (100 + v.stack + p.growth * v.j + v.blocks + v.height) ≤ l := h.four_span.trans h.group
    omega
  have hr : v.group ≤ l := Nat.lt_two_pow_self.le.trans h.group
  have he : 2 ^ w ≤ (2 : ℕ) ^ (4 * l) := calc
    _ ≤ _ := hw
    _ ≤ 2 ^ v.group * (2 ^ 5 * 2 ^ (l * 2) * 2 ^ v.stack * 2 ^ v.blocks) :=
      Nat.mul_le_mul ho (Nat.mul_le_mul_right _
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ hm') Nat.lt_two_pow_self))
    _ ≤ _ := by
      simp only [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
  exact (Nat.pow_le_pow_iff_right (by decide)).mp he

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

section
/-! # Uniform ranges of the intermediate widths and the input size -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Suits

variable {δ a b ξ : ℝ} {p : Design δ} {M n m T₀ : ℕ} {v : Levels p M}
  (ok : v.Suits n T₀ a b ξ)
include ok

theorem width_window {i : ℕ} (hi : i ≤ v.j) :
    T₀ ≤ v.width i ∧ v.width i ≤ (Nat.clog 2 n) ^ 4 := by
  obtain ⟨_, _, _, _, _, _, lo, _, _, _, up, _⟩ := ok
  rw [v.width_eq]
  refine ⟨lo.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)), le_trans ?_ up⟩
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left _ hi) _)

theorem input_size (nm : n ≤ m) (upper : (m : ℝ) ≤ (n : ℝ) ^ (11 / 10 : ℝ)) : 0 < m ∧ m ≤ n ^ 2 := by
  have hn : 0 < n := by
    have hw := ok.2.1
    by_contra h
    rw [show n = 0 by omega] at hw
    norm_num at hw
  have le : (m : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := calc
    _ ≤ _ := upper
    _ ≤ (n : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
    _ = _ := Real.rpow_two _
  exact ⟨hn.trans_le nm, by exact_mod_cast le⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Suits
end

/-! # Bounds on fixed-degree control expressions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

variable {δ : ℝ} {p : Design δ} {R n T₀ : ℕ} {a b ξ : ℝ} {v : Levels p R}

theorem Levels.box_le_group_power {E q : ℕ} (he : E ≤ q * p.groupRate) :
    v.box E ≤ 2 ^ (q * v.group) := by
  unfold Levels.box Levels.group
  rw [← mul_assoc]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ he)

theorem Levels.Suits.group_power_le_width (ok : v.Suits n T₀ a b ξ)
    {q : ℕ} (hq : (p.groupRate * q : ℕ) * a ≤ b) :
    (2 : ℝ) ^ (q * v.group) ≤ (2 : ℝ) ^ (2 * p.groupRate * q) * (v.finalWidth : ℝ) := by
  let h : ℝ := Nat.clog 2 n
  have hh : 1 ≤ h := ok.2.1.le
  have hpos : 0 < h := zero_lt_one.trans_le hh
  obtain ⟨_, _, _, _, ht, _, _, _, _, _, _, hg, _⟩ := ok
  have hp : h ^ ((p.groupRate * q : ℕ) * a) ≤ v.finalWidth := calc
    _ ≤ h ^ b := Real.rpow_le_rpow_of_exponent_le hh hq
    _ ≤ (2 : ℝ) ^ v.stack := ht
    _ ≤ (v.finalWidth : ℝ) := by
      unfold Levels.finalWidth
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right ..)
  calc
    _ = ((2 : ℝ) ^ v.group) ^ q := by rw [mul_comm q, pow_mul]
    _ ≤ ((2 : ℝ) ^ (2 * p.groupRate) * h ^ (p.groupRate * a)) ^ q := pow_le_pow_left₀ (by positivity) hg _
    _ = (2 : ℝ) ^ (2 * p.groupRate * q) * h ^ ((p.groupRate * q : ℕ) * a) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast hpos.le, Nat.cast_mul]
      rw [mul_right_comm (p.groupRate : ℝ)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

/-- If a controller uses a fixed power of a record length plus the
price of wide routing, choose the sorting tolerance before taking
this power. -/
theorem power_with_routing {x W h τ σ : ℝ} {e : ℕ}
    (hx : 1 ≤ x) (hW : 0 ≤ W) (hh : 1 ≤ h) (hτ : 0 ≤ τ)
    (hprice : W ≤ h ^ τ) (hσ : (e : ℝ) * τ ≤ σ) :
    (x + W) ^ e ≤ (2 * x) ^ e * h ^ σ := by
  have hpos : 0 < h := zero_lt_one.trans_le hh
  have hpow : 1 ≤ h ^ τ := Real.one_le_rpow hh hτ
  have xx : x + W ≤ 2 * x * h ^ τ := by
    have h₁ : x ≤ x * h ^ τ := le_mul_of_one_le_right (zero_le_one.trans hx) hpow
    have h₂ : W ≤ x * h ^ τ := hprice.trans (le_mul_of_one_le_left (by positivity) hx)
    linarith only [h₁, h₂]
  calc
    _ ≤ (2 * x * h ^ τ) ^ e := pow_le_pow_left₀ (by linarith) xx _
    _ = (2 * x) ^ e * h ^ (τ * (e : ℝ)) := by rw [mul_pow, Real.rpow_mul_natCast hpos.le]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hh (by simpa only [mul_comm] using hσ)

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Uniform assembly with one common arity ceiling -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels

open Assembly Filter

variable {δ : ℝ} {p : Design δ} {M T₀ : ℕ} {a b ξ : ℝ}

theorem installed_trace (ha : 0 < a) (ha' : a ≤ 1) (hδ : 0 < δ)
    (C : ℝ) (hC : 1 ≤ C) (r q B s : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p M) (m : ℕ), v.Suits n T₀ a b ξ →
      ∀ (F : Type) [Field F] (x y : Wire) (k : Val x → Val y → F),
      let h : ℝ := Nat.clog 2 n
      let W := C * (Real.log h) ^ r * h ^ (a * δ / 12)
      let budget := W * v.expense h m (wd x + wd y) q
      let cap := W * (p.D * (v.finalWidth : ℝ))
      let menu := B * (Nat.clog 2 n) ^ s
      ∀ (P : Layer F (copies x v.batch) (copies y v.batch))
        (good : ℕ → Layer F (copies x v.batch) (copies y v.batch) → Prop)
        (i : P.State) (z : F),
        good 0 P →
        (fun a b => z * (P.graph i).eval a b) = power k v.batch →
        ((140 * (P.snapshot.port.width + v.batch * (wd x + wd y)) + 1 : ℕ) : ℝ) ≤ budget →
        (∀ j < v.j, ∀ Q, good j Q →
          ∃ (R : Layer F (copies x v.batch) (copies y v.batch)) (L : Finset (Table F)) (u t : ℕ),
            good (j + 1) R ∧ L.card ≤ menu ∧ (u : ℝ) ≤ cap ∧ (t : ℝ) ≤ budget ∧
              Transforms F u L Q.snapshot R.snapshot t) →
        (∀ Q, good v.j Q →
          ∃ (L : Finset (Table F)) (u t : ℕ), L.card ≤ menu ∧ (u : ℝ) ≤ cap ∧ (t : ℝ) ≤ budget ∧
            Finishes F u L Q.snapshot t) →
        v.Installed n m (p.groupRate * q) a k := by
  have hl := (Real.tendsto_log_atTop.comp Shaving.tendsto_height).eventually_ge_atTop 1
  filter_upwards [hl, Levels.installed_of_round_budget (p:=p) (R:=M) (T₀:=T₀) (b:=b)
    (ξ:=ξ) ha ha' hδ C r q B s] with n hlog bound v m ok F _ x y k
  dsimp only
  intro P good i z h₀ exactPower initial next final
  let h : ℝ := Nat.clog 2 n
  let W := C * (Real.log h) ^ r * h ^ (a * δ / 12)
  let budget := W * v.expense h m (wd x + wd y) q
  let cap := W * (p.D * (v.finalWidth : ℝ))
  let menu := B * (Nat.clog 2 n) ^ s
  have hh : 1 ≤ h := ok.2.1.le
  have hW : 1 ≤ W := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hlog)) (Real.one_le_rpow hh (by positivity))
  have hD : (3 : ℝ) ≤ p.D := by exact_mod_cast (show 3 ≤ p.D by have := p.large; omega)
  have hwidth : (1 : ℝ) ≤ v.finalWidth := by
    exact_mod_cast (show 1 ≤ v.finalWidth by unfold Levels.finalWidth; exact Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hcap : (3 : ℝ) ≤ cap := hD.trans
    ((le_mul_of_one_le_right (by positivity) hwidth).trans (le_mul_of_one_le_left (by positivity) hW))
  have hpos : 0 ≤ cap := (by norm_num : (0 : ℝ) ≤ 3).trans hcap
  have hbudget : 0 ≤ budget := by unfold budget W Levels.expense Levels.finalBudget; positivity
  have next' j (hj : j < v.j) Q (hq₀ : good j Q) :
      ∃ (R : Layer F (copies x v.batch) (copies y v.batch)) (L : Finset (Table F)) (u t : ℕ),
        good (j + 1) R ∧ L.card ≤ menu ∧ u ≤ ⌊cap⌋₊ ∧ (t : ℝ) ≤ budget ∧
          Transforms F u L Q.snapshot R.snapshot t := by
    obtain ⟨R, L, u, t, hR, hL, hu, ht, hnet⟩ := next j hj Q hq₀
    exact ⟨R, L, u, t, hR, hL, Nat.le_floor hu, ht, hnet⟩
  have final' Q (hq₀ : good v.j Q) :
      ∃ (L : Finset (Table F)) (u t : ℕ), L.card ≤ menu ∧ u ≤ ⌊cap⌋₊ ∧ (t : ℝ) ≤ budget ∧
        Finishes F u L Q.snapshot t := by
    obtain ⟨L, u, t, hL, hu, ht, hnet⟩ := final Q hq₀
    exact ⟨L, u, t, hL, Nat.le_floor hu, ht, hnet⟩
  obtain ⟨I, hu, hL, hs⟩ := P.install_with_bounds good h₀ ok.1
    (Nat.le_floor (by simpa using hcap)) i z exactPower budget hbudget initial next' final'
  refine bound v m ok F x y k I hL ?_ ?_
  · simpa only [abs_of_nonneg (zero_le_one.trans hC)] using hs
  · have hc : (I.u : ℝ) ≤ cap := by rw [hu]; exact Nat.floor_le hpos
    have hsum : (1 : ℝ) ≤ (v.j : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) v.j
      linarith
    have hle : (I.u : ℝ) ≤ (v.j + 2) * cap :=
      hc.trans (le_mul_of_one_le_left hpos hsum)
    simpa only [abs_of_nonneg (zero_le_one.trans hC)] using hle

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end

/-! # A polylogarithmic bound on payload-index lengths -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
open Filter

variable {δ : ℝ}

theorem eventual_span_log (p : Design δ) (M extra : ℕ) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p M) (T₀ : ℕ) (b ξ : ℝ),
      b ≤ 1 → v.Suits n T₀ a b ξ →
      ((v.span + extra : ℕ) : ℝ) ≤ J * (Real.log (Nat.clog 2 n)) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / a)
  have hak : 1 ≤ a * k := by rw [mul_comm]; exact (div_le_iff₀ ha).mp hk
  let c : ℕ := 100 + 2 * (1 + p.gain * k) + p.growth + M * (1 + p.gain * k) + 2 * p.steps * p.groupRate
  let d : ℝ := 2 / Real.log 2
  let J : ℝ := (c : ℝ) * d ^ 2 + extra
  have hJ : 0 ≤ J := by unfold J; positivity
  have hl := (Real.tendsto_log_atTop.comp Shaving.tendsto_height).eventually_ge_atTop 1
  refine ⟨J, hJ, ?_⟩
  filter_upwards [hl] with n hn v T₀ b ξ hb ok
  let h : ℝ := Nat.clog 2 n
  change 1 ≤ Real.log h at hn
  have logs : 0 ≤ Real.log h := zero_le_one.trans hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj : (v.j : ℝ) ≤ d * Real.log h := ok.rounds_log ha'
  have ha1 : 1 ≤ (Real.log h) ^ 2 := one_le_pow₀ hn
  have hs : (v.span : ℝ) ≤ (c : ℝ) * (v.j : ℝ) ^ 2 := by
    have := ok.span_square hb hak
    change v.span ≤ c * v.j ^ 2 at this
    exact_mod_cast this
  push_cast
  calc
    _ ≤ (c : ℝ) * (v.j : ℝ) ^ 2 + extra := add_le_add hs le_rfl
    _ ≤ (c : ℝ) * (d * Real.log h) ^ 2 + (extra : ℝ) * (Real.log h) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hj _) (by positivity))
        (le_mul_of_one_le_right (by positivity) ha1)
    _ = _ := by unfold J; ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.Levels
end
