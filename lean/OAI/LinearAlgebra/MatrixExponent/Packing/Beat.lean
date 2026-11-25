import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift
import OAI.LinearAlgebra.MatrixExponent.Packing.TetherHost
import OAI.LinearAlgebra.MatrixExponent.Tagged.Hard
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag
import Mathlib.Data.Nat.Log

/-! # Quantitative reduction bounds for one subround and one reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open HostNet

variable {F : Type} [Field F]

def Gadget.ratio (P : Gadget F) : ℝ := 1 - 1 / (8 * (P.b : ℝ))

theorem Gadget.ratio_bounds (P : Gadget F) : 0 ≤ P.ratio ∧ P.ratio < 1 := by
  have hp : (1 : ℝ) ≤ P.b := by exact_mod_cast P.pos
  have hb : 1 ≤ 8 * (P.b : ℝ) := by linarith
  exact ⟨sub_nonneg.mpr ((div_le_one (by linarith)).mpr hb), sub_lt_self _ (by positivity)⟩

def degreePower : ℕ := 2700

namespace Reduction

/-- Each elementary step adds exactly the old bit incidences. -/
private theorem mass_step {m n K x : ℕ} {z : ℝ} (hn : n = m + 2 * x)
    (hK : 1 ≤ K) (hz : 0 ≤ z) : (n : ℝ) ≤ m + 2 * (K : ℝ) * (x + z) := by
  rw [hn]
  push_cast
  have h : (1 : ℝ) ≤ K := by exact_mod_cast hK
  exact add_le_add le_rfl
    (mul_le_mul (by linarith) (le_add_of_nonneg_right hz) (by positivity) (by positivity))

private theorem scale {h k K r a H : ℕ} {B σ : ℝ} (hb : 0 ≤ B) (hk : 2 ^ k ≤ K)
    (ha : a + 1 * r ≤ h) (hr : K ≤ 2 ^ r) (slack : (K : ℝ) * B * (H * 2 ^ h : ℕ) ≤ σ * (2 : ℝ) ^ r) :
    a + k ≤ h ∧ (2 : ℝ) ^ k * B * (H * 2 ^ a : ℕ) ≤ σ := by
  have hkr : k ≤ r := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hk.trans hr)
  refine ⟨by omega, le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 ^ r)⟩
  apply le_trans _ slack
  push_cast
  rw [mul_assoc, mul_assoc (H : ℝ), ← pow_add]
  gcongr
  · exact_mod_cast hk
  · norm_num
  · omega

private theorem cubic {D : ℕ} (h : 3 ≤ D) : 4 * D ≤ D ^ 3 := by
  have hs : 4 ≤ D ^ 2 := by nlinarith
  exact (Nat.mul_le_mul_right D hs).trans_eq (pow_succ _ _).symm

theorem power_growth {D : ℕ} (hd : 3 ≤ D) (n z : ℕ) (hz : z = 3 * n) : (4 * D) ^ n ≤ D ^ z := by
  subst z
  rw [pow_mul]
  exact Nat.pow_le_pow_left (cubic hd) _

theorem subround (P₀ : Gadget F) (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    ∃ K, ∀ (L : Type) [Field L] [Algebra F L],
      Reduction L Δ (Δ ^ degreePower) P₀.b 1 degreePower K P₀.ratio 1 := by
  let k := 256 * (coreBins Δ + 1)
  let T₀ := P₀.copies * P₀.shapes.card + 1
  let B₀ := 9 * (4 * Δ) ^ 300 * 2 ^ k
  let K := 2 * (Δ + 1) + 2 ^ k + T₀ + B₀
  have hpos : 1 ≤ k := by unfold k; omega
  have hk : 2 ^ k ≤ K := by unfold K; omega
  have : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow _ _ (by decide)
  have htwo : 2 ≤ K := by unfold K; omega
  have grow (D : ℕ) (hd : 3 ≤ D) : (4 * D) ^ 900 ≤ D ^ degreePower := power_growth hd 900 degreePower rfl
  refine ⟨K, fun L₀ _ _ => ?_⟩
  let P := P₀.extend L₀
  change Reduction L₀ Δ (Δ ^ degreePower) P.b 1 degreePower K P.ratio 1
  refine ⟨P.pos, by omega, fun D h => Nat.pow_le_pow_left h _, P.ratio_bounds.1, by norm_num, ?_⟩
  intro T _ x y L h u G z r a D M B σ hz hu huB hD hb hσ ha hr slack budget
  subst u
  have hzu : z ≤ P.b * z := Nat.le_mul_of_pos_left _ P.pos
  have hB : 0 < B := (Nat.cast_pos.mpr (hz.trans_le hzu)).trans_le huB
  obtain ⟨ha', hs⟩ := scale hB.le hk ha hr slack
  obtain ⟨I, _, q, hc, he, ho⟩ := G.subround P hz a k Δ D (by omega) hD hpos ha' B σ hB hb
    Nat.lt_two_pow_self.le hs
  refine ⟨I, inferInstance, q, hc.trans ?_, he, fun i => ?_⟩
  · have hE : Fintype.card G.E ≤ M := by
      have hx : (G.X : ℝ) ≤ (M : ℝ) * z := (le_add_of_nonneg_right (add_nonneg L.total_nonneg hσ)).trans budget
      have ht : G.X ≤ M * z := by exact_mod_cast hx
      exact Nat.le_of_mul_le_mul_right ((Nat.mul_le_mul_left _ hzu).trans ht) hz
    have ht : T₀ ≤ 2 ^ K := (show T₀ ≤ K by unfold K; omega).trans Nat.lt_two_pow_self.le
    rw [pow_mul]
    exact (Nat.pow_le_pow_left ht _).trans (Nat.pow_le_pow_right (by positivity) hE)
  · obtain ⟨hs, hb, hw, hp, hmass, tk⟩ := ho i
    refine ⟨hp, (G.seats_le (q i) (by omega) hs).trans (Nat.mul_le_mul_right _ htwo),
      hb.mono (grow _ hΔ) (grow _ (hΔ.trans hD)) ?_, by simpa only [Gadget.ratio, one_mul],
      mass_step hmass (by omega) (add_nonneg L.total_nonneg hσ), tk.mono (by unfold K; omega)⟩
    have ht : (B₀ : ℝ) ≤ K := Nat.cast_le.mpr (by unfold K; omega)
    simpa only [B₀, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right ht hB.le

theorem degree_reset {D Y : ℕ} (hD : 3 ≤ D) :
    3 + terminalWidth D Y ≤ D ^ (900 + Y + 1) := by
  have a : (4 * D) ^ 300 ≤ D ^ 900 := power_growth hD 300 900 rfl
  have b : Y ≤ D ^ Y := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _)
  have c : 3 ≤ D ^ (900 + Y) := hD.trans (Nat.le_self_pow (by omega) _)
  have ht : terminalWidth D Y ≤ D ^ (900 + Y) := by
    rw [pow_add]
    exact Nat.mul_le_mul a b
  rw [pow_succ]
  exact (Nat.add_le_add c ht).trans (by rw [← mul_two]; exact Nat.mul_le_mul_left _ (by omega))

theorem reset {Y w Δ : ℕ} (R : Rotor F Y w) (hY : 0 < Y) (hw : 0 < w)
    (hΔ : 3 ≤ Δ) (enough : 4 * coreBins Δ ≤ Y)
    (c : ℝ) (hc : 0 ≤ c) (hR : (Fintype.card R.E : ℝ) ≤ c * Y * w) :
    ∃ K, ∀ (L : Type) [Field L] [Algebra F L],
      Reduction L Δ 3 1 1 (900 + Y + 1) K (2 * resetWidth c w) (2 * resetWidth c w) := by
  obtain ⟨k, step⟩ := HostNet.reset hY hw (by omega) enough c hc
  let K := resetPositions R Δ + 89 * 2 ^ k + 1
  have hk : 2 ^ k ≤ K := by unfold K; omega
  have hW : 0 ≤ resetWidth c w := by unfold resetWidth; positivity
  refine ⟨K, fun L₀ _ _ => ?_⟩
  refine ⟨by decide, by unfold K; omega,
    fun D hd => (hΔ.trans hd).trans (Nat.le_self_pow (by omega) _), by positivity, by positivity, ?_⟩
  intro T _ x y L h u G z r a D M B σ hz hu huB hD hb hσ ha hr slack _
  rw [one_mul] at hu
  subst z
  have hB := (Nat.cast_nonneg u).trans huB
  obtain ⟨ha', hs⟩ := scale hB hk ha hr slack
  obtain ⟨Q, he, hq, hd, hw, hp, hmass, tk⟩ := step L₀ (R.extend L₀) hR T x y L h a u D B σ G ha' hD hb hz huB hs
  change Fintype.card Q.V ≤ resetPositions R Δ * 2 ^ (h - a) * Fintype.card G.V at hq
  change G.Tracks Q (resetPositions R Δ + 1) at tk
  refine Expands.single Q he hp ⟨(G.seats_le Q (by omega) hq).trans ?_,
    hd.mono le_rfl (degree_reset (hΔ.trans hD)) ?_, hw.trans ?_,
    mass_step hmass (by unfold K; omega) (add_nonneg L.total_nonneg hσ),
    tk.mono (by unfold K; omega)⟩
  · exact Nat.mul_le_mul_right _ (by unfold K; omega)
  · apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast (show 89 * 2 ^ k ≤ K by unfold K; omega)
  · linarith [mul_nonneg hW hσ]

end Reduction
end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
/-!
# Choosing the number of subrounds and the rotor

Choose a sufficiently small tagged-permutation exponent, then let the
number of subrounds grow in fixed strides. The address length grows
exponentially in the number of strides. Its small power grows as
`2 ^ i`, which the contraction absorbs geometrically.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Filter

private theorem enough_rows (D k t : ℕ) (ht : 0 < t) (Δ : ℕ) (hΔ : Δ ≤ D ^ (k ^ t)) :
    4 * Δ * 2 ^ (64 * Nat.clog 2 (2 * Δ)) ≤ 2 ^ (2 ^ (131 * (D + 1) * (k + 1) * t)) := by
  let j := (D + 1) * (k + 1) ^ t
  have hj : 0 < j := by unfold j; positivity
  have hd : Δ ≤ 2 ^ j := calc
    _ ≤ D ^ (k ^ t) := hΔ
    _ ≤ (2 ^ D) ^ (k ^ t) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ ≤ 2 ^ j := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul (Nat.le_succ D) (Nat.pow_le_pow_left (Nat.le_succ k) _))
  have hl : Nat.clog 2 (2 * Δ) ≤ j + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    omega
  have hy : 131 * j ≤ 2 ^ (131 * (D + 1) * (k + 1) * t) := calc
    _ ≤ (131 * (D + 1) * (k + 1)) ^ t := by
      rw [mul_pow]
      simpa only [j, mul_assoc] using
        Nat.mul_le_mul_right ((k + 1) ^ t) (Nat.le_self_pow ht.ne' (131 * (D + 1)))
    _ ≤ _ := by rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  calc
    _ ≤ 2 ^ 2 * 2 ^ j * 2 ^ (64 * Nat.clog 2 (2 * Δ)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hd)
    _ ≤ _ := by
      rw [← pow_add, ← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Either source of inexpensive rotors supplies arbitrarily large
address lengths with a polynomially bounded payload. -/
private theorem frequent_tag {F : Type} [Field F] (tag : Radix.WideTag F ∨ ¬Tagged.Hard F)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ (A : ℕ) (C : ℝ), ∀ n : ℕ, ∃ y m : ℕ, 0 < y ∧ n ≤ y ∧ Radix.Tag F y (y ^ A) m ∧
      (m : ℝ) ≤ C * (2 : ℝ) ^ y * (y ^ A : ℕ) * (y : ℝ) ^ ζ := by
  rcases tag with h | h
  · obtain ⟨A, _, C, h⟩ := h ζ hζ
    refine ⟨A, C, fun n => ?_⟩
    obtain ⟨m, hm, hc⟩ := h (n + 1) _ (by omega) le_rfl
    exact ⟨n + 1, m, by omega, by omega, hm, hc⟩
  refine ⟨1, 1, fun n => ?_⟩
  simp only [pow_one, one_mul]
  by_contra! bad
  apply h
  refine ⟨ζ, hζ, ?_⟩
  filter_upwards [eventually_gt_atTop n] with y hy m hm
  exact (bad y m (by omega) hy.le hm).le

/-- Choose the contraction count from the available address length.
Even an arbitrarily sparse sequence of good lengths suffices. -/
theorem choose_rotor {F : Type} [Field F] (tag : Radix.WideTag F ∨ ¬Tagged.Hard F) (D k : ℕ)
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hB : 0 ≤ B) :
    ∃ (t y w : ℕ) (R : Rotor F (2 ^ y) w) (c : ℝ),
      0 < t ∧ 0 < w ∧ 1 ≤ c ∧
      (Fintype.card R.V : ℝ) + Fintype.card R.E ≤ c * (2 : ℝ) ^ y * w ∧
      (∀ Δ ≤ D ^ (k ^ t), 4 * Δ * 2 ^ (64 * Nat.clog 2 (2 * Δ)) ≤ 2 ^ y) ∧
      B * (1 + c + Nat.clog 2 w) * ρ ^ t ≤ 1 / 2 := by
  let b := 131 * (D + 1) * (k + 1)
  have hb : 0 < b := by unfold b; positivity
  obtain ⟨p, hp, hsmall⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ').eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 4))).exists
  let ζ : ℝ := 1 / ((b : ℝ) * p)
  have hζ : 0 < ζ := by unfold ζ; positivity
  obtain ⟨A, C, htag⟩ := frequent_tag tag hζ
  let K := B * (2 + 6 * |C| + b * p * A)
  have tend := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ 2 * ρ ^ p by positivity)
    (show 2 * ρ ^ p < 1 by linarith)
  have lim := tend.const_mul K
  rw [mul_zero] at lim
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp ((eventually_gt_atTop 0).and
    (lim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)))
  let u := 2 ^ (b * p)
  have hu : 1 < u := one_lt_pow₀ (by decide) (Nat.mul_pos hb hp).ne'
  obtain ⟨y, m, hy, hlo, hnet, hs⟩ := htag (u ^ i₀)
  let i := Nat.log u y
  obtain ⟨hi, hdec⟩ := hi₀ i (Nat.le_log_of_pow_le hu hlo)
  let t := p * i
  have ht : 0 < t := Nat.mul_pos hp hi
  have low : 2 ^ (b * t) ≤ y := by
    rw [show b * t = (b * p) * i from (mul_assoc _ _ _).symm, pow_mul]
    exact Nat.pow_log_le_self u hy.ne'
  have up : y ≤ 2 ^ (b * p * (i + 1)) := by
    rw [pow_mul]
    exact (Nat.lt_pow_of_log_lt hu (Nat.lt_succ_self i)).le
  have scale : (y : ℝ) ^ ζ ≤ 2 * (2 : ℝ) ^ i := calc
    _ ≤ ((2 : ℝ) ^ (b * p * (i + 1))) ^ ζ :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast up) hζ.le
    _ = (2 : ℝ) ^ (i + 1) := by
      rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast 2 (i + 1)]
      congr 1
      simp only [ζ, Nat.cast_mul]
      field_simp
    _ = _ := pow_succ' _ _
  have clog : Nat.clog 2 (y ^ A) ≤ b * p * A * 2 ^ i := by
    apply Nat.clog_le_of_le_pow
    refine (Nat.pow_le_pow_left up A).trans ?_
    rw [← pow_mul, mul_right_comm (b * p)]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ Nat.lt_two_pow_self)
  obtain ⟨R, hv, he⟩ := Rotor.of_tag hnet
  let c := 1 + 6 * |C| * (2 : ℝ) ^ i
  refine ⟨t, y, y ^ A, R, c, ht, by positivity, le_add_of_nonneg_right (by positivity), ?_, ?_, ?_⟩
  · rw [hv]
    have hem : (Fintype.card R.E : ℝ) ≤ 2 * m := by
      exact_mod_cast (show Fintype.card R.E ≤ 2 * m by omega)
    calc
      _ ≤ 3 * (m : ℝ) := by linarith
      _ ≤ 3 * (|C| * (2 : ℝ) ^ y * (y ^ A : ℕ) * (2 * (2 : ℝ) ^ i)) := by
        apply mul_le_mul_of_nonneg_left (hs.trans ?_) (by norm_num)
        gcongr
        exact le_abs_self _
      _ ≤ _ := by unfold c; nlinarith [show 0 ≤ (2 : ℝ) ^ y * (y ^ A : ℕ) by positivity]
  · intro Δ hΔ
    exact (enough_rows D k t ht Δ hΔ).trans (Nat.pow_le_pow_right (by decide) low)
  · have ha : (Nat.clog 2 (y ^ A) : ℝ) ≤ (b : ℝ) * p * A * (2 : ℝ) ^ i := by exact_mod_cast clog
    have hfact : 1 + c + Nat.clog 2 (y ^ A) ≤ (2 + 6 * |C| + (b : ℝ) * p * A) * (2 : ℝ) ^ i := by
      unfold c
      linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := i)]
    calc
      _ ≤ B * ((2 + 6 * |C| + (b : ℝ) * p * A) * (2 : ℝ) ^ i) * ρ ^ t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfact hB) (by positivity)
      _ = K * (2 * ρ ^ p) ^ i := by simp only [t, K, mul_pow, pow_mul, mul_assoc]
      _ ≤ _ := hdec.le

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Reduction of core width

Use a fixed number of contracting subrounds followed by a degree
reset. Choose the rotor large enough for the degree at the last
subround and cheap enough for the contraction to absorb its cost.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open HostNet

variable {F : Type} [Field F]

namespace Reduction

theorem relax {Δ Δ' b n e K K' : ℕ} {ρ ρ' C C' : ℝ}
    (p : Reduction F Δ Δ' b n e K ρ C) (hK : K ≤ K') (hρ : ρ ≤ ρ') (hc : C ≤ C') :
    Reduction F Δ Δ' b n e K' ρ' C' := by
  refine ⟨p.unit, p.overhead.trans_le hK, p.degree, p.factor.trans hρ, p.loss.trans hc, ?_⟩
  intro T _ x y L h u G z r a D M B σ hz hu hub hd hb hs ha hr hsl hbud
  have hB := (Nat.cast_nonneg u).trans hub
  have hKB := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) hB
  have he := p.run G z r a D M B σ hz hu hub hd hb hs ha (hK.trans hr)
    ((mul_le_mul_of_nonneg_right hKB (Nat.cast_nonneg _)).trans hsl) hbud
  refine he.mono (Nat.mul_le_mul_right _ hK) ?_
  rintro Q ⟨hs', hb', hw, hm, t⟩
  exact ⟨hs'.trans (Nat.mul_le_mul_right _ hK), hb'.mono le_rfl le_rfl hKB,
    hw.trans (add_le_add (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_right hc (add_nonneg L.total_nonneg hs))),
    hm.trans (by have := L.total_nonneg; gcongr), t.mono hK⟩

theorem subrounds (P : Gadget F) (Δ : ℕ) (hΔ : 3 ≤ Δ) (t : ℕ) (ht : 0 < t) :
    ∃ K, ∀ (L : Type) [Field L] [Algebra F L],
      Reduction L Δ (Δ ^ (degreePower ^ t)) (P.b ^ t) t (degreePower ^ t) K (P.ratio ^ t) t := by
  have : 0 < degreePower := by decide
  induction t, ht using Nat.le_induction with
  | base => simpa only [pow_one, Nat.cast_one] using subround P Δ hΔ
  | succ t _ ih =>
    obtain ⟨K, p⟩ := ih
    obtain ⟨K', q⟩ := subround P (Δ ^ (degreePower ^ t)) (hΔ.trans (Nat.le_self_pow (by positivity) _))
    refine ⟨fee K (P.ratio ^ t) t * K', fun L _ _ => ?_⟩
    have h := (p L).comp (q L)
    rw [← pow_mul Δ (degreePower ^ t) degreePower, ← pow_succ degreePower, ← pow_succ P.b, ← pow_succ' P.ratio] at h
    refine h.relax le_rfl le_rfl ?_
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add_left (mul_le_of_le_one_left (Nat.cast_nonneg _) P.ratio_bounds.2.le) _

end Reduction

/-- Core width is halved up to the frozen charge and slack. The overheads
are uniform across field extensions and depend only on the incoming
core degree and the ground field. -/
theorem beat (tag : Radix.WideTag F ∨ ¬Tagged.Hard F) (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    ∃ (b n e K : ℕ) (C : ℝ), 0 < n ∧ 0 < e ∧
      ∀ (L : Type) [Field L] [Algebra F L], Reduction L Δ 3 b n e K (1 / 2) C := by
  obtain ⟨P⟩ := gadget_exists F
  obtain ⟨t, y, w, R, c, ht, hw, hc, hsize, en, hdecay⟩ :=
    choose_rotor tag Δ degreePower P.ratio 250 P.ratio_bounds.1 P.ratio_bounds.2 (by norm_num)
  obtain ⟨K, p⟩ := Reduction.subrounds P Δ hΔ t ht
  have : 0 < degreePower := by decide
  let D := Δ ^ (degreePower ^ t)
  have hd : 3 ≤ D := hΔ.trans (Nat.le_self_pow (by positivity) _)
  have enough : 4 * coreBins D ≤ 2 ^ y := by
    simpa only [coreBins, mul_assoc] using en D le_rfl
  have hR : (Fintype.card R.E : ℝ) ≤ c * (2 ^ y : ℕ) * w := by
    push_cast
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsize
  obtain ⟨K', q⟩ := Reduction.reset R (by positivity) hw hd enough c (by linarith) hR
  have bound : 2 * resetWidth c w ≤ 250 * (1 + c + Nat.clog 2 w) := by
    unfold resetWidth
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 w)]
  have decrease := (mul_le_mul_of_nonneg_right bound (pow_nonneg P.ratio_bounds.1 t)).trans hdecay
  exact ⟨_, _, _, _, _, by positivity, by positivity,
    fun L _ _ => ((p L).comp (q L)).relax le_rfl decrease le_rfl⟩

/-- Repeat a fixed beat while keeping both rates and the subdivision explicit. -/
theorem Reduction.iterate {Δ b n e K : ℕ} {C : ℝ} (p : Reduction F Δ 3 b n e K (1 / 2) C)
    (hΔ : 3 ≤ Δ) (he : 0 < e) (t : ℕ) (ht : 0 < t) :
    Reduction F Δ 3 (b ^ t) (n * t) (e ^ t) ((fee K (1 / 2) C) ^ t) ((1 / 2) ^ t) (2 * C) := by
  let H := Reduction.fee K (1 / 2) C
  have w : Reduction F Δ Δ b n e K (1 / 2) C := by
    refine ⟨p.unit, p.overhead, fun D hd => hd.trans (Nat.le_self_pow he.ne' D),
      p.factor, p.loss, ?_⟩
    intro T _ x y L h u G z r a D M B σ hz hu hub hd hb hs ha hr hsl hbud
    exact (p.run G z r a D M B σ hz hu hub hd hb hs ha hr hsl hbud).mono le_rfl
      (fun q hq => ⟨hq.1, hq.2.1.mono hΔ le_rfl le_rfl, hq.2.2⟩)
  have hk : K ≤ H := by unfold H Reduction.fee; omega
  have hit (t : ℕ) (ht : 0 < t) :
      Reduction F Δ 3 (b ^ t) (n * t) (e ^ t) (H ^ t) ((1 / 2) ^ t) (2 * C * (1 - (1 / 2) ^ t)) := by
    induction t, ht using Nat.le_induction with
    | base =>
      simp only [Nat.succ_eq_add_one, Nat.zero_add, pow_one, mul_one, show 2 * C * (1 - (1 / 2)) = C by ring]
      exact p.relax hk le_rfl le_rfl
    | succ t _ ih =>
      have h := w.comp ih
      rw [show Reduction.fee K (1 / 2) C = H from rfl,
        ← pow_succ' b, ← pow_succ' e, ← pow_succ' H, ← pow_succ (1 / 2 : ℝ),
        show n + n * t = n * (t + 1) by ring,
        show (1 / 2 : ℝ) ^ t * C + 2 * C * (1 - (1 / 2) ^ t) = 2 * C * (1 - (1 / 2) ^ (t + 1)) by rw [pow_succ]; ring] at h
      exact h
  refine (hit t ht).relax le_rfl le_rfl ?_
  exact mul_le_of_le_one_right (mul_nonneg (by norm_num) p.loss)
    (sub_le_self _ (by positivity))

/-- Iterate with a bounded additive loss and only exponential growth
of the subdivision, load and full-degree exponent. -/
theorem beats (tag : Radix.WideTag F ∨ ¬Tagged.Hard F) (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    ∃ (b n e H : ℕ) (C : ℝ), 0 < n ∧ 0 < e ∧ ∀ t : ℕ, 0 < t →
      ∀ (L : Type) [Field L] [Algebra F L], Reduction L Δ 3 (b ^ t) (n * t) (e ^ t) (H ^ t) ((1 / 2) ^ t) C := by
  obtain ⟨b, n, e, K, C, hn, he, step⟩ := beat tag Δ hΔ
  let H := Reduction.fee K (1 / 2) C
  refine ⟨b, n, e, H, 2 * C, hn, he, ?_⟩
  intro t ht L₀ _ _
  exact (step L₀).iterate hΔ he t ht

end OAI.LinearAlgebra.MatrixExponent.Packing
end
