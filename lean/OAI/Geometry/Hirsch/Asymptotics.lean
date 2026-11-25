import OAI.Geometry.Hirsch.Statements

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch

theorem eventually_power {exp : ℝ} (hp : 0 < exp) (bound : ℝ) :
    ∀ᶠ n : ℕ in atTop, bound ≤ (n : ℝ) ^ exp :=
  ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop bound)

theorem eventually_dominate {lo hi : ℝ} (hh : lo < hi) (factor : ℝ) :
    ∀ᶠ n : ℕ in atTop, factor * (n : ℝ) ^ lo ≤ (n : ℝ) ^ hi := by
  filter_upwards [eventually_power (sub_pos.mpr hh) factor, eventually_gt_atTop 0] with n hn hp
  calc
    _ ≤ (n : ℝ) ^ (hi - lo) * (n : ℝ) ^ lo := by gcongr
    _ = _ := by rw [← Real.rpow_add (by positivity), sub_add_cancel]

theorem eventually_scale {base : ℕ} (hb : 2 ≤ base) (threshold : ℕ)
    {lo hi : ℝ} (hl : 0 < lo) (hh : lo < hi) :
    ∀ᶠ n : ℕ in atTop, ∃ height ≥ threshold,
      (n : ℝ) ^ lo ≤ (base ^ height : ℕ) ∧ (base ^ height : ℕ) ≤ (n : ℝ) ^ hi := by
  have hb' : 1 < (base : ℝ) := by exact_mod_cast hb
  filter_upwards [eventually_power hl ((base : ℝ) ^ threshold),
    eventually_dominate hh base] with n hn hd
  obtain ⟨height, hle, hlt⟩ := exists_nat_pow_near ((one_le_pow₀ hb'.le).trans hn) hb'
  refine ⟨height + 1, ?_, by simpa using hlt.le, ?_⟩
  · by_contra! he
    exact (hn.trans_lt hlt).not_ge (pow_le_pow_right₀ hb'.le he.le)
  · rw [Nat.cast_pow, pow_succ']
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hd

def accuracy (stage : ℕ) : ℝ := 1 / (stage + 2 : ℝ)

theorem accuracy_pos (stage : ℕ) : 0 < accuracy stage := by unfold accuracy; positivity

theorem accuracy_le_one (stage : ℕ) : accuracy stage ≤ 1 := by
  unfold accuracy
  apply (div_le_one (by positivity)).mpr
  linarith

theorem accuracy_anti : Antitone accuracy := by
  intro first last hh
  unfold accuracy
  gcongr

theorem exists_stage {eps : ℝ} (he : 0 < eps) (exp : ℝ) :
    ∃ stage : ℕ, accuracy stage ≤ eps ∧ exp ≤ stage := by
  obtain ⟨stage, hs⟩ := exists_nat_gt (max (1 / eps) exp)
  refine ⟨stage, ?_, (le_max_right _ _).trans hs.le⟩
  have hh := (div_le_iff₀ he).mp ((le_max_left _ _).trans hs.le)
  unfold accuracy
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

def StageBound (moves n stage : ℕ) (ex : Example) : Prop :=
  ex.poly.sys.Regular ∧ ex.poly.facetCount = n ∧
    (ex.poly.dimension : ℝ) ≤ (n : ℝ) ^ accuracy stage ∧
    ∀ first last : ex.poly.V, (n : ℝ) ^ (accuracy stage - 1) ≤ ex.obj.gap first last →
      (n : ℝ) ^ (stage : ℝ) ≤ ex.poly.dist moves first last

theorem stage_of_cap (cap : CapLemma) (moves : ℕ → ℕ) (hm : ∀ n, 0 < moves n)
    (sub : Subpolynomial moves) (stage : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ ex, StageBound (moves n) n stage ex := by
  let eps := accuracy stage
  have he : 0 < eps := accuracy_pos stage
  have he' : eps ≤ 1 := accuracy_le_one stage
  let lo := 1 - eps / 2
  let hi := 1 - eps / 4
  let eta := eps / 8
  let degree := 2 * stage + 2
  have hl : 0 < lo := by unfold lo; linarith
  have hh : lo < hi := by unfold lo hi; linarith
  have ht : 0 < eta := by unfold eta; linarith
  have hu : eta < eps := by unfold eta; linarith
  have hb : hi * (1 + eta) < 1 := by unfold hi eta; nlinarith
  obtain ⟨base, hbase, gamma, hg, hseed⟩ := cap degree (by omega) eta ht (hu.trans_le he')
  obtain ⟨threshold, hseed⟩ := eventually_atTop.mp hseed
  filter_upwards [eventually_ge_atTop 6, eventually_scale hbase threshold hl hh,
    sub _ (mul_pos hl hg), eventually_dominate hb 2, eventually_dominate hu 3,
    eventually_power (half_pos he) 9] with n hn hex hmove hbudget hdim hgap
  obtain ⟨height, hheight, lower, upper⟩ := hex
  let scale := base ^ height
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp : (0 : ℝ) < n := by linarith
  have hs : (0 : ℝ) < scale := (Real.rpow_pos_of_pos hp _).trans_le lower
  have hsn : (scale : ℝ) ≤ n := by
    apply upper.trans
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (show hi ≤ 1 by unfold hi; linarith)
  obtain ⟨poly, obj, reg, hd, hf, cost⟩ := hseed height hheight 1 le_rfl
  have hallow : moves n ≤ ⌊(scale : ℝ) ^ gamma⌋₊ := by
    apply Nat.le_floor
    rw [Real.rpow_mul hp.le] at hmove
    exact hmove.trans (Real.rpow_le_rpow (by positivity) lower hg.le)
  have hf' : 2 * poly.facetCount ≤ n := by
    rw [Real.rpow_mul hp.le, Real.rpow_one] at hbudget
    have hc := Real.rpow_le_rpow hs.le upper (show 0 ≤ 1 + eta by linarith)
    simp only [Nat.cast_one, one_mul] at hf
    change (poly.facetCount : ℝ) ≤ (scale : ℝ) ^ (1 + eta) at hf
    exact_mod_cast (show 2 * (poly.facetCount : ℝ) ≤ n by linarith)
  obtain ⟨pad, hreg, hpd, hpf⟩ := polygon (n - poly.facetCount) (by omega)
  refine ⟨⟨poly.product pad, poly.productObjective pad obj⟩,
    poly.product_regular pad reg hreg, ?_, ?_, ?_⟩
  · change (poly.product pad).facetCount = _
    rw [poly.product_facetCount pad reg hreg, hpf]
    omega
  · change ((poly.product pad).dimension : ℝ) ≤ (n : ℝ) ^ eps
    rw [poly.product_dimension pad reg hreg, hpd, Nat.cast_add, Nat.cast_ofNat]
    have hc := hd.trans (Real.rpow_le_rpow hs.le hsn ht.le)
    linarith [Real.one_le_rpow hn' ht.le]
  intro first last hsep
  let src := poly.project pad first
  let dst := poly.project pad last
  change (n : ℝ) ^ (eps - 1) ≤ obj.gap src dst at hsep
  have hsep' : 9 ≤ (scale : ℝ) * obj.gap src dst := by
    calc
      _ ≤ (n : ℝ) ^ (eps / 2) := hgap
      _ = (n : ℝ) ^ lo * (n : ℝ) ^ (eps - 1) := by
        rw [← Real.rpow_add hp]
        congr 1
        unfold lo
        ring
      _ ≤ _ := mul_le_mul lower hsep (by positivity) hs.le
  have hc := (cost src dst).2
  simp only [Nat.cast_one, one_mul] at hc
  have hpow : (stage : ℝ) ≤ lo * (degree - 1 : ℕ) := by
    have heq : degree - 1 = 2 * stage + 1 := by omega
    rw [heq]
    push_cast
    unfold lo
    nlinarith [Nat.cast_nonneg (α := ℝ) stage]
  calc
    _ ≤ (n : ℝ) ^ (lo * (degree - 1 : ℕ)) := Real.rpow_le_rpow_of_exponent_le hn' hpow
    _ ≤ (scale : ℝ) ^ (degree - 1) := by
      rw [Real.rpow_mul hp.le, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) lower _
    _ ≤ (scale : ℝ) ^ (degree - 1) * max 0 (scale * obj.gap src dst - 8) :=
      le_mul_of_one_le_right (by positivity) (le_max_of_le_right (by linarith))
    _ ≤ _ := hc.trans (Nat.cast_le.mpr ((poly.dist_anti reg (hm n) hallow src dst).trans
      (poly.product_dist pad reg hreg (hm n) first last)))

theorem main_of_cap (cap : CapLemma) : MainTheorem := by
  classical
  intro moves hm sub
  let good := fun n stage => ∃ ex, StageBound (moves n) n stage ex
  have hev : ∀ stage, ∀ᶠ n in atTop, good n stage := stage_of_cap cap moves hm sub
  let level := fun n => Nat.findGreatest (good n) n
  obtain ⟨_, defaultEx, _⟩ := (hev 0).exists
  let family := fun n => if hh : good n (level n) then hh.choose else defaultEx
  have hlevel : ∀ stage, ∀ᶠ n in atTop,
      stage ≤ level n ∧ StageBound (moves n) n (level n) (family n) := by
    intro stage
    filter_upwards [hev stage, eventually_ge_atTop stage] with n hn hle
    have hh : good n (level n) := Nat.findGreatest_spec hle hn
    exact ⟨Nat.le_findGreatest hle hn, by simpa [family, hh] using hh.choose_spec⟩
  have separated : ∀ alpha : ℝ, alpha < 1 → ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ first last : (family n).poly.V, (n : ℝ) ^ (-alpha) ≤ (family n).obj.gap first last →
        (n : ℝ) ^ exponent ≤ (family n).poly.dist (moves n) first last := by
    intro alpha ha exponent
    obtain ⟨stage, hs, he⟩ := exists_stage (sub_pos.mpr ha) exponent
    filter_upwards [hlevel stage, eventually_ge_atTop 1] with n hn hp first last hgap
    have hp' : (1 : ℝ) ≤ n := by exact_mod_cast hp
    have hh := (accuracy_anti hn.1).trans hs
    have hsep := (Real.rpow_le_rpow_of_exponent_le hp'
      (show accuracy (level n) - 1 ≤ -alpha by linarith)).trans hgap
    exact (Real.rpow_le_rpow_of_exponent_le hp' (he.trans (Nat.cast_le.mpr hn.1))).trans
      (hn.2.2.2.2 first last hsep)
  refine ⟨family, ?_, ?_, ?_, fun alpha _ ha => separated alpha ha⟩
  · filter_upwards [hlevel 0] with n hn
    exact ⟨hn.2.1.simple, (family n).poly.connected hn.2.1 le_rfl, hn.2.2.1⟩
  · intro eps he
    obtain ⟨stage, hs, _⟩ := exists_stage he 0
    filter_upwards [hlevel stage, eventually_ge_atTop 1] with n hn hp
    exact hn.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp)
      ((accuracy_anti hn.1).trans hs))
  · intro exponent
    filter_upwards [separated 0 zero_lt_one exponent] with n hn
    exact hn _ _ (by simp [Polytope.Objective.gap_extremes])

end OAI.Geometry.Hirsch
