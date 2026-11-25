import OAI.LinearAlgebra.MatrixExponent.Shaving.FieldStage
import OAI.LinearAlgebra.MatrixExponent.Lookup.Network
import OAI.LinearAlgebra.MatrixExponent.Shaving.Defs
import OAI.LinearAlgebra.MatrixExponent.Network.Matrix
import OAI.LinearAlgebra.MatrixExponent.Distinctness

section
/-!
# Quantitative reduction of trivalent compression to stages and lookup

`R j d s u` describes the intermediate realization after `j` stages,
with `d` copies, size `s` counting stations and ports, and arity at most
`u`. It can track the admissible table dictionary at each stage.
`T d m` describes a trivalent realization over the original field.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Shaving
open Filter

/-- One arity reduction with an integer size budget. -/
def Stage (R : ℕ → ℕ → ℕ → ℕ → Prop) (n e J : ℕ) (β δ a ξ : ℝ) : Prop :=
  let h : ℝ := Nat.clog 2 n
  ∀ j d s u M : ℕ, j < J → 1 ≤ d → R j d s u →
    (u : ℝ) ≤ h ^ (β + (1 + δ) * a * j) →
    s ≤ M → n ≤ M → (M : ℝ) ≤ (n : ℝ) ^ (11 / 10 : ℝ) →
    (d : ℝ) * e ≤ M * h ^ (-(2 * a)) →
    ∃ r s' u' : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ (n : ℝ) ^ ξ ∧ R (j + 1) (d * r) s' u' ∧
      (s' : ℝ) ≤ (M : ℝ) * r * h ^ (-((1 - δ) * a)) ∧
      (u' : ℝ) ≤ h ^ (β + (1 + δ) * a * (j + 1))

/-- Batch lookup followed by descent from a degree `O(log h)` extension. -/
def Finish (T : ℕ → ℕ → Prop) (R : ℕ → ℕ → ℕ → ℕ → Prop) (n J : ℕ)
    (ρ C : ℝ) : Prop :=
  let h : ℝ := Nat.clog 2 n
  ∀ d s u : ℕ, 1 ≤ d → R J d s u →
    ∃ m : ℕ, T (d * 2 ^ u) m ∧
      (m : ℝ) ≤ C * (Real.log h) ^ 2 * (2 : ℝ) ^ u * s * (1 + (u : ℝ)) ^ ρ

/-- In the large-cost case the descending size envelope leaves enough
room for every exterior bit, even after rounding down. -/
private theorem budget {m n e d h η x a : ℝ} (hn : 1 ≤ n) (hne : n ≤ e)
    (hd : 1 ≤ d) (hh : 1 ≤ h) (hm : e * h ^ η ≤ m)
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hs : 2 * a + x ≤ η)
    (hm' : m ≤ n ^ (21 / 20 : ℝ)) (hd' : d ≤ n ^ (1 / 40 : ℝ))
    (hfour : 4 ≤ n ^ (1 / 40 : ℝ)) :
    let M := ⌊4 * m * d * h ^ (-x)⌋₊
    n ≤ (M : ℝ) ∧ (M : ℝ) ≤ n ^ (11 / 10 : ℝ) ∧ d * e ≤ M * h ^ (-(2 * a)) := by
  have he : 1 ≤ e := hn.trans hne
  have hm₀ : 0 ≤ m := le_trans (by positivity) hm
  have hh₀ : 0 < h := zero_lt_one.trans_le hh
  have hn₀ : 0 < n := zero_lt_one.trans_le hn
  let z := d * e * h ^ (2 * a)
  have hnz : n ≤ z := calc
    n ≤ e := hne
    _ ≤ d * e := le_mul_of_one_le_left (by positivity) hd
    _ ≤ z := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hh (by positivity))
  have hz : z ≤ m * d * h ^ (-x) := by
    rw [Real.rpow_neg hh₀.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc
      z * h ^ x = d * (e * h ^ (2 * a + x)) := by
        rw [Real.rpow_add hh₀]; unfold z; ring
      _ ≤ d * (e * h ^ η) := by gcongr
      _ ≤ m * d := by rw [mul_comm m]; gcongr
  let M := ⌊4 * m * d * h ^ (-x)⌋₊
  have hzM : z ≤ (M : ℝ) := by
    have hf : 4 * m * d * h ^ (-x) < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  refine ⟨hnz.trans hzM, ?_, ?_⟩
  · calc
      (M : ℝ) ≤ 4 * m * d * h ^ (-x) := Nat.floor_le (by positivity)
      _ ≤ 4 * m * d := mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos hh (neg_nonpos.mpr hx))
      _ ≤ n ^ (1 / 40 : ℝ) * n ^ (21 / 20 : ℝ) * n ^ (1 / 40 : ℝ) := by gcongr
      _ = n ^ (11 / 10 : ℝ) := by rw [← Real.rpow_add hn₀, ← Real.rpow_add hn₀]; norm_num
  · change d * e ≤ (M : ℝ) * h ^ (-(2 * a))
    rw [Real.rpow_neg hh₀.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact hzM

private theorem stages {R : ℕ → ℕ → ℕ → ℕ → Prop} {n m e J : ℕ}
    {β δ a ξ η : ℝ} (ha : 0 < a) (hd : δ ≤ 1) (hξ : 0 < ξ)
    (hroom : 2 * a + (1 - δ) * a * J ≤ η) (hcard : ξ * J ≤ 1 / 40)
    (hn : 1 ≤ n) (hne : n ≤ e) (hfour : 4 ≤ (n : ℝ) ^ (1 / 40 : ℝ))
    (hm : (m : ℝ) ≤ (n : ℝ) ^ (21 / 20 : ℝ))
    (hinit : ∃ s u : ℕ, R 0 1 s u ∧ s ≤ 4 * m ∧ u ≤ 3)
    (hstage : Stage R n e J β δ a ξ) :
    let h : ℝ := Nat.clog 2 n
    1 ≤ h → 3 ≤ h ^ β → (e : ℝ) * h ^ η ≤ m →
    ∃ d s u : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (n : ℝ) ^ (ξ * J) ∧ R J d s u ∧
      (s : ℝ) ≤ 4 * m * d * h ^ (-((1 - δ) * a * J)) ∧
      (u : ℝ) ≤ h ^ (β + (1 + δ) * a * J) := by
  intro h hh hthree he
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  have hh₀ : 0 < h := zero_lt_one.trans_le hh
  let x := (1 - δ) * a
  have hx : 0 ≤ x := mul_nonneg (sub_nonneg.mpr hd) ha.le
  suffices ∀ j : ℕ, j ≤ J → ∃ d s u : ℕ,
      1 ≤ d ∧ (d : ℝ) ≤ (n : ℝ) ^ (ξ * j) ∧ R j d s u ∧
      (s : ℝ) ≤ 4 * m * d * h ^ (-(x * j)) ∧
      (u : ℝ) ≤ h ^ (β + (1 + δ) * a * j) from this J le_rfl
  intro j hj
  induction j with
  | zero =>
    obtain ⟨s, u, hR, hs, hu⟩ := hinit
    refine ⟨1, s, u, le_rfl, by simp, hR, ?_, ?_⟩
    · simpa using (by exact_mod_cast hs : (s : ℝ) ≤ 4 * m)
    · simpa using (show (u : ℝ) ≤ 3 by exact_mod_cast hu).trans hthree
  | succ j ih =>
    have hj' : j ≤ J := Nat.le_of_succ_le hj
    obtain ⟨d, s, u, hd₁, hdj, hR, hs, hu⟩ := ih hj'
    have hξj : ξ * j ≤ 1 / 40 :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hj') hξ.le).trans hcard
    have hd' := hdj.trans (Real.rpow_le_rpow_of_exponent_le hn₁ hξj)
    have hroom' : 2 * a + x * j ≤ η := by
      apply le_trans _ hroom
      change 2 * a + x * j ≤ 2 * a + x * J
      gcongr
    let M := ⌊4 * (m : ℝ) * d * h ^ (-(x * j))⌋₊
    obtain ⟨hnM, hM, heM⟩ := budget hn₁ (by exact_mod_cast hne) (by exact_mod_cast hd₁)
      hh he ha.le (by positivity) hroom' hm hd' hfour
    obtain ⟨r, s', u', hr, hr', hR', hs', hu'⟩ :=
      hstage j d s u M hj hd₁ hR hu (Nat.le_floor hs) (Nat.cast_le.mp hnM) hM heM
    refine ⟨d * r, s', u', Nat.mul_pos hd₁ hr, ?_, hR', ?_, by simpa using hu'⟩
    · rw [Nat.cast_succ, mul_add, mul_one, Real.rpow_add hn₀, Nat.cast_mul]
      exact mul_le_mul hdj hr' (by positivity) (by positivity)
    · have hM' : (M : ℝ) ≤ 4 * m * d * h ^ (-(x * j)) := Nat.floor_le (by positivity)
      calc
        _ ≤ (M : ℝ) * r * h ^ (-x) := hs'
        _ ≤ (4 * m * d * h ^ (-(x * j))) * r * h ^ (-x) := by gcongr
        _ = 4 * m * (d * r : ℕ) * h ^ (-(x * (j.succ : ℝ))) := by
          rw [Nat.cast_succ, Nat.cast_mul, mul_add, mul_one, neg_add, Real.rpow_add hh₀]
          ring

private theorem lookup_cost {s u m d : ℕ} {C h ρ γ x b : ℝ}
    (hh : 1 ≤ h) (hC : 0 < C) (hρ : 0 < ρ) (hb : 0 ≤ b)
    (hs : (s : ℝ) ≤ 4 * m * d * h ^ (-x)) (hu : (u : ℝ) ≤ h ^ b)
    (hcost : (4 * (2 : ℝ) ^ ρ * C) * (Real.log h) ^ 2 ≤ h ^ γ)
    (hgap : 2 * γ = x - b * ρ) :
    C * (Real.log h) ^ 2 * (2 : ℝ) ^ u * s * (1 + (u : ℝ)) ^ ρ ≤
      (d * 2 ^ u : ℕ) * ((m : ℝ) * h ^ (-γ)) := by
  have hh₀ : 0 < h := zero_lt_one.trans_le hh
  have hu' : (1 + (u : ℝ)) ^ ρ ≤ (2 : ℝ) ^ ρ * h ^ (b * ρ) := by
    rw [Real.rpow_mul hh₀.le, ← Real.mul_rpow (by norm_num) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hρ.le
    linarith [Real.one_le_rpow hh hb]
  calc
    _ ≤ C * (Real.log h) ^ 2 * (2 : ℝ) ^ u * (4 * m * d * h ^ (-x)) *
        ((2 : ℝ) ^ ρ * h ^ (b * ρ)) := by gcongr
    _ = (d * 2 ^ u : ℕ) * (m : ℝ) * h ^ (-x + b * ρ) *
        ((4 * (2 : ℝ) ^ ρ * C) * (Real.log h) ^ 2) := by
      rw [Real.rpow_add hh₀]; push_cast; ring
    _ ≤ (d * 2 ^ u : ℕ) * (m : ℝ) * h ^ (-x + b * ρ) * h ^ γ := by gcongr
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hh₀, show -x + b * ρ + γ = -γ by linarith, mul_assoc]

/-- All parameters except the power bound are fixed before the replication
slack `κ` is specified. The cutoff for `n` is uniform in the input tensor. -/
theorem shave {ρ η : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) (hη : 0 < η) :
    ∃ γ δ β : ℝ, 0 < γ ∧ 0 < δ ∧ δ ≤ 1 / 10 ∧ 0 < β ∧ β ≤ 1 / 2 ∧
    ∀ α : ℝ, 0 < α → ∃ (a : ℝ) (J : ℕ), 0 < a ∧ a < α ∧ 0 < J ∧
      β + (1 + δ) * a * J ≤ 1 / 2 ∧
    ∀ κ : ℝ, 0 < κ → ∃ ξ : ℝ, 0 < ξ ∧ ∀ C : ℝ, 0 < C →
    ∀ᶠ n : ℕ in atTop, ∀ (m e : ℕ) (T : ℕ → ℕ → Prop) (R : ℕ → ℕ → ℕ → ℕ → Prop),
      n ≤ e → (m : ℝ) ≤ (n : ℝ) ^ (21 / 20 : ℝ) → T 1 m →
      (∃ s u : ℕ, R 0 1 s u ∧ s ≤ 4 * m ∧ u ≤ 3) →
      Stage R n e J β δ a ξ → Finish T R n J ρ C →
      ∃ d m' : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (n : ℝ) ^ κ ∧ T d m' ∧
        let h : ℝ := Nat.clog 2 n
        (m' : ℝ) ≤ d * ((m : ℝ) * h ^ (-γ) + (e : ℝ) * h ^ η) := by
  let δ := (1 - ρ) / 10
  have hd : 0 < δ := by dsimp [δ]; linarith
  have hd' : δ ≤ 1 / 10 := by dsimp [δ]; linarith
  let A := min 1 η / 8
  have hA : 0 < A := by unfold A; positivity
  have hA₁ : A ≤ 1 / 8 := by dsimp [A]; linarith [min_le_left 1 η]
  have hAη : 3 * A ≤ η := by dsimp [A]; linarith [min_le_right 1 η]
  let β := δ * A
  let b := β + (1 + δ) * A
  let x := (1 - δ) * A
  let γ := (x - b * ρ) / 2
  have hβ : 0 < β := mul_pos hd hA
  have hβb : β ≤ b := le_add_of_nonneg_right (by positivity)
  have hb : b ≤ 1 / 2 := by
    unfold b β
    nlinarith
  have hgap : 2 * γ = x - b * ρ := by unfold γ; ring
  have hγ : 0 < γ := by
    have hw : 0 < 1 - δ - (1 + 2 * δ) * ρ := by
      have : δ * ρ ≤ δ := mul_le_of_le_one_right hd.le hρ'.le
      unfold δ at *
      linarith
    apply half_pos
    convert mul_pos hw hA using 1
    unfold x b β
    ring
  refine ⟨γ, δ, β, hγ, hd, hd', hβ, hβb.trans hb, ?_⟩
  intro α hα
  obtain ⟨J, hJ⟩ := exists_nat_gt (A / α)
  have hJ₀ : 0 < (J : ℝ) := lt_trans (by positivity) hJ
  have hJ₁ : 1 ≤ J := Nat.cast_pos.mp hJ₀
  let a := A / J
  have ha : 0 < a := div_pos hA hJ₀
  have ha' : a < α := (div_lt_iff₀ hJ₀).2 (by linarith [(div_lt_iff₀ hα).1 hJ])
  have haA : a ≤ A := div_le_self hA.le (by exact_mod_cast hJ₁)
  have hAJ : a * J = A := div_mul_cancel₀ _ hJ₀.ne'
  have hxJ : (1 - δ) * a * J = x := by rw [mul_assoc, hAJ]
  have hbJ : β + (1 + δ) * a * J = b := by rw [mul_assoc, hAJ]
  have hroom : 2 * a + (1 - δ) * a * J ≤ η := by
    rw [hxJ]
    unfold x
    nlinarith
  refine ⟨a, J, ha, ha', hJ₁, hbJ.trans_le hb, ?_⟩
  intro κ hκ
  let ξ := min (κ / 2) (1 / 40) / J
  have hξ : 0 < ξ := by unfold ξ; positivity
  have hξJ : ξ * J = min (κ / 2) (1 / 40) := div_mul_cancel₀ _ hJ₀.ne'
  refine ⟨ξ, hξ, ?_⟩
  intro C hC
  have hfour : ∀ᶠ n : ℕ in atTop, 4 ≤ (n : ℝ) ^ (1 / 40 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  filter_upwards [eventually_ge_atTop 1, tendsto_height.eventually_ge_atTop 1, hfour,
    ((tendsto_rpow_atTop hβ).comp tendsto_height).eventually_ge_atTop 3,
    batch_le (half_pos hκ), tendsto_height.eventually (cost_le (4 * (2 : ℝ) ^ ρ * C) hγ)]
    with n hn hh hf hthree hbatch hcost m e T R hne hm hT hinit hstage hfinish
  let h : ℝ := Nat.clog 2 n
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  -- Small input cost already meets the target without any replication.
  by_cases he : (m : ℝ) ≤ e * h ^ η
  · refine ⟨1, m, le_rfl, by simpa using Real.one_le_rpow hn₁ hκ.le, hT, ?_⟩
    simp only [Nat.cast_one, one_mul]
    exact he.trans (le_add_of_nonneg_left (by positivity))
  obtain ⟨d, s, u, hd₁, hdξ, hR, hs, hu⟩ :=
    stages ha (by linarith) hξ hroom (hξJ.trans_le (min_le_right _ _))
      hn hne hf hm hinit hstage hh hthree (le_of_not_ge he)
  rw [hxJ] at hs
  rw [hbJ] at hu
  have hdκ := hdξ.trans
    (Real.rpow_le_rpow_of_exponent_le hn₁ (hξJ.trans_le (min_le_left _ _)))
  have huκ := hbatch u (hu.trans (Real.rpow_le_rpow_of_exponent_le hh hb))
  obtain ⟨m', hT', hm'⟩ := hfinish d s u hd₁ hR
  refine ⟨d * 2 ^ u, m', Nat.mul_pos hd₁ (by positivity), ?_, hT', ?_⟩
  · push_cast
    calc
      _ ≤ (n : ℝ) ^ (κ / 2) * (n : ℝ) ^ (κ / 2) :=
        mul_le_mul hdκ huκ (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity), add_halves]
  · exact (hm'.trans (lookup_cost hh hC hρ (hβ.le.trans hβb) hs hu hcost hgap)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))

end OAI.LinearAlgebra.MatrixExponent.Shaving
end

section
/-!
# From wide networks to compression

Packing, substitution and field descent preserve the exterior labels.
The same field is used throughout each sequence of arity reductions.
-/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

variable {F K : Type} [Field F] [Field K] {x y : Wire}

private theorem Labeled.join {k : Val x → Val y → K} {d r B s u : ℕ}
    (h : Labeled (power (power k d) r) B s u) : Labeled (power k (d * r)) B s u := by
  obtain ⟨L, hL, h⟩ := h
  obtain ⟨f, hf, ef⟩ := (Rewire.joinCopies x d r).inverse
  obtain ⟨g, hg, eg⟩ := (Rewire.joinCopies y d r).inverse
  have he : (fun a b => power (power k d) r (f a) (g b)) = power k (d * r) := by
    funext a b
    rw [← power_join, (ef _ a).mpr rfl, (eg _ b).mpr rfl]
  exact ⟨L, hL, he ▸ (h.pre hf).post hg⟩

private theorem stages {n J : ℕ} {B : ℕ → ℕ} {β δ a ξ : ℝ}
    (h : ∀ j : ℕ, j < J → ArityStep K n (B j) (B (j + 1)) (β + (1 + δ) * a * j) δ a ξ)
    (k : Val x → Val y → K) :
    Shaving.Stage (fun j d s u => Labeled (power k d) (B j) s u)
      n (wd x + wd y) J β δ a ξ := by
  intro j d s u M hj _ hk hu hs hn hM he
  obtain ⟨r, s', u', hr, hr', hnet, hsize, hmax⟩ :=
    h j hj _ _ _ s u M hk hu hs hn hM (by simpa only [wd_copies, ← Nat.mul_add, Nat.cast_mul] using he)
  refine ⟨r, s', u', hr, hr', hnet.join, hsize, ?_⟩
  rwa [show β + (1 + δ) * a * (j + 1) = (β + (1 + δ) * a * j) + (1 + δ) * a by ring]

private theorem map_power (f : F →+* K) (k : Val x → Val y → F) (d : ℕ) :
    power (fun a b => f (k a b)) d = fun a b => f (power k d a b) := by
  induction d with
  | zero => simp [power]
  | succ d ih => funext a b; simp only [power, map_mul, ih]

-- Include exposed bits in the cost of the network after descent.
private theorem finish_cost {u s e d v v' D : ℕ} {A C H ρ : ℝ}
    (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (hd : 1 ≤ D) (hD : (D : ℝ) ≤ C * Real.log H)
    (hs : d * e ≤ s) (hv : (v : ℝ) ≤ A * (2 : ℝ) ^ u * s * (1 + (u : ℝ)) ^ ρ)
    (hv' : v' ≤ 288 * D ^ 2 * v) :
    ((v' + d * 2 ^ u * e : ℕ) : ℝ) ≤
      289 * A * C ^ 2 * (Real.log H) ^ 2 * (2 : ℝ) ^ u * s * (1 + (u : ℝ)) ^ ρ := by
  let X := A * (2 : ℝ) ^ u * s * (1 + (u : ℝ)) ^ ρ
  have hX : 0 ≤ X := by unfold X; positivity
  have hrp : 1 ≤ (1 + (u : ℝ)) ^ ρ := Real.one_le_rpow (by simp) hρ
  have hbits : ((d * 2 ^ u * e : ℕ) : ℝ) ≤ X := by
    have hde : (d : ℝ) * e ≤ s := by exact_mod_cast hs
    push_cast
    calc
      _ = 1 * (2 : ℝ) ^ u * (d * (e : ℝ)) * 1 := by ring
      _ ≤ X := by unfold X; gcongr
  have hd' : 1 ≤ (D : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hd)
  have hv'' : (v' : ℝ) ≤ 288 * (D : ℝ) ^ 2 * v := by exact_mod_cast hv'
  rw [Nat.cast_add]
  calc
    _ ≤ 288 * (D : ℝ) ^ 2 * X + (D : ℝ) ^ 2 * X :=
      add_le_add (hv''.trans (mul_le_mul_of_nonneg_left hv (by positivity)))
        (hbits.trans (le_mul_of_one_le_left hX hd'))
    _ = 289 * (D : ℝ) ^ 2 * X := by ring
    _ ≤ 289 * (C * Real.log H) ^ 2 * X := by gcongr
    _ = _ := by unfold X; ring

/-- Compression of arbitrary tensors specializes to the independent lists. -/
theorem Compresses.lists (h : Compresses F) : Compression (Realizes F) := by
  have ht : Tendsto listBits atTop atTop :=
    tendsto_atTop_mono (fun w => show w ≤ listBits w by
      unfold listBits
      have : 1 ≤ 2 ^ w := Nat.one_le_pow w 2 (by decide)
      nlinarith) tendsto_id
  intro η hη
  obtain ⟨γ, hγ, h⟩ := h η hη
  refine ⟨γ, hγ, fun κ hκ => ?_⟩
  filter_upwards [ht.eventually (h κ hκ)] with w hw t m ht' hreal hm
  obtain ⟨v, hv, rfl⟩ := hreal
  specialize hw _ _ _ v hv
  simp only [wd_lists, wd, add_zero] at hw
  obtain ⟨d, m', hd, hd', ⟨v', hv', heq⟩, hc⟩ :=
    hw (Nat.le_mul_of_pos_left _ ht') hm
  refine ⟨d, m', hd, hd', ⟨v', hv'.power_lists, ?_⟩, ?_⟩
  · simpa only [wd_lists, wd, add_zero, Nat.mul_left_comm, Nat.mul_assoc] using heq
  · simpa only [Nat.cast_mul] using hc

/-- Theorem 2.1 from ordinary-width sorting and the one-stage arity
reduction. Batch lookup, descent and iteration are all proved here. -/
theorem compresses_of_stages {p : ℝ} (hp : 1 < p) (hp' : p < 2)
    (sort : Lookup.Sorting F p) (reduce : ArityReduction F) : Compresses F := by
  obtain ⟨A, hA, lookup⟩ := Lookup.lookup_network hp.le sort
  have hρ : 0 < p - 1 := by linarith
  intro η hη
  obtain ⟨γ, δ, β, hγ, hd, hd', hb, hb', h⟩ := Shaving.shave hρ (by linarith) hη
  obtain ⟨α, hα, step⟩ := reduce δ β hd hd' hb hb'
  obtain ⟨a, J, ha, ha', hJ, hmax, h⟩ := h α hα
  refine ⟨γ, hγ, fun κ hκ => ?_⟩
  obtain ⟨ξ, hξ, h⟩ := h κ hκ
  obtain ⟨C, hC, red⟩ := step a J ha ha' hJ hmax ξ hξ
  filter_upwards [red, h (289 * A * C ^ 2) (by positivity)] with n hn hh x y k v hv
  dsimp only
  intro he hm
  obtain ⟨K, _, _, _, B, hdeg, hstep⟩ := hn
  let e := wd x + wd y
  let k' := fun a b => algebraMap F K (k a b)
  let R := fun j d s u => Labeled (power k' d) (B j) s u
  apply hh (v + e) e (PowerSize k) R he hm
  · exact ⟨1 * v, hv.power 1, by simp [e]⟩
  · obtain ⟨s, hs, hw⟩ := ((hv.map (algebraMap F K)).power 1).wide
    refine ⟨s, 3, ⟨∅, by simp, ?_⟩, by omega, le_rfl⟩
    simpa only [Finset.coe_empty] using hw
  · exact stages hstep k'
  · intro d s u _ hnet
    obtain ⟨L, _, hw⟩ := hnet
    have hw' : d * e ≤ s := by
      simpa only [wd_copies, ← Nat.mul_add] using hw.width
    obtain ⟨v₁, h₁, cost₁⟩ := lookup K inferInstance inferInstance u _ _ _ _ s hw
    have hr := h₁.rewire (Rewire.joinCopies x d (2 ^ u)) (Rewire.joinCopies y d (2 ^ u))
      (power_join k' d (2 ^ u))
    rw [show power k' (d * 2 ^ u) = _ from map_power (algebraMap F K) k _] at hr
    obtain ⟨v₂, h₂, cost₂⟩ := hr.descend
    exact ⟨v₂ + d * 2 ^ u * e, ⟨v₂, h₂, rfl⟩,
      finish_cost hA hρ.le Module.finrank_pos hdeg hw' cost₁ cost₂⟩

end OAI.LinearAlgebra.MatrixExponent
end
