import OAI.Geometry.Hirsch.DriverBudget

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch

def SchedulerTheorem : Prop :=
  ∀ degree rate : ℕ, ∃ base labels growth extra overhead : ℕ, 2 ≤ base ∧ 0 < labels ∧
    (2 * labels) ^ (growth * rate) ≤ base ∧ ∀ height : ℕ, 0 < height →
      let span := growth * height + extra
      ∃ bank : ℕ → Bank,
        (∀ idx ≤ degree, ∀ limit : ℕ, (bank idx).Tracer limit ((limit + 1) * (2 * labels) ^ span) span) ∧
        ∀ idx < degree, (bank idx).Schedules (bank (idx + 1)) (base ^ height) labels overhead span

theorem Bank.Schedules.mono {bank client : Bank} {count labels overhead span larger}
    (hh : bank.Schedules client count labels overhead span) (hle : span ≤ larger) :
    bank.Schedules client count labels overhead larger := by
  intro prog hp hm buckets hb ep
  obtain ⟨sch, hf⟩ := hh prog hp hm buckets hb ep
  exact ⟨sch, hf.mono le_rfl le_rfl hle⟩

theorem supply_of_schedules {degree scale depth root labels overhead span : ℕ} (bank : ℕ → Bank)
    (hn : 0 < scale) (hl : 0 < labels) (hr : 4 * labels + overhead + 4 ≤ root)
    (hw : (2 * labels) ^ (7 ^ degree * span) ≤ root)
    (ht : ∀ idx ≤ degree, (bank idx).Tracer root ((root + 1) * (2 * labels)^span) span)
    (hs : ∀ idx < degree, (bank idx).Schedules (bank (idx + 1)) scale labels overhead span) :
    Nonempty (Supply degree scale depth root) := by
  let bound := fun stage : ℕ => 7 ^ stage * span
  have mono : Monotone bound := fun _ _ hh =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hh)
  have hspan : ∀ stage, span ≤ bound stage := fun _ => Nat.le_mul_of_pos_left _ (by positivity)
  have hvol : ∀ stage, root ≤ volume root depth stage :=
    fun stage => Nat.le_self_pow (exponent_pos depth stage).ne' _
  have hweight : ∀ stage ≤ degree, (2 * labels) ^ bound stage ≤ root :=
    fun _ hh => (Nat.pow_le_pow_right (by omega) (mono hh)).trans hw
  refine ⟨⟨bank, bound, mono, ?_, ?_⟩⟩
  · intro idx hi
    obtain ⟨prog, ha, hv, hp, hh⟩ := ht idx hi
    refine ⟨prog, ha, hv, hp.trans ?_, fun coord => (hh coord).trans (hspan 0)⟩
    have he : (2 * labels)^span ≤ root := by simpa [bound] using hweight 0 (Nat.zero_le _)
    change _ ≤ root ^ 4
    calc
      _ ≤ root ^ 2 * root ^ 2 := Nat.mul_le_mul (by nlinarith) (he.trans (Nat.le_self_pow (by decide) _))
      _ = _ := by ring
  · intro stage idx hi rows hrows
    have hb : bound (stage + 1) = 7 * bound stage := by simp [bound, pow_succ', mul_assoc]
    rw [hb]
    exact ((hs idx (by omega)).mono (hspan stage)).drives hn hl (hr.trans (hvol stage))
      (volume_mono (by omega) depth (by omega)) ((hweight stage (by omega)).trans (hvol degree)) hrows

theorem supplies_of_scheduler (scheduler : SchedulerTheorem) : Supplies := by
  intro degree depth gamma hg
  obtain ⟨rate, hr⟩ := exists_nat_gt ((7 ^ degree : ℕ) / gamma)
  have hr' : (0 : ℝ) < rate := lt_trans (by positivity) hr
  let exp := (7 ^ degree : ℕ) / (rate : ℝ)
  have he : exp < gamma := (div_lt_iff₀ hr').mpr (by linarith [(div_lt_iff₀ hg).mp hr])
  obtain ⟨base, labels, growth, extra, overhead, hb, hl, hw, hs⟩ := scheduler degree rate
  have ht : Tendsto (fun height : ℕ => base ^ height) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  let factor := (2 * labels) ^ (7 ^ degree * extra)
  refine ⟨base, hb, ?_⟩
  filter_upwards [eventually_gt_atTop 0, ht.eventually (eventually_power hg (4 * labels + overhead + 4 : ℕ)),
    ht.eventually (eventually_dominate he factor)] with height hp hlarge hdom
  let scale := base ^ height
  let root := ⌊(scale : ℝ)^gamma⌋₊ + 1
  let span := growth * height + extra
  obtain ⟨bank, htr, hsch⟩ := hs height hp
  have hroot : (scale : ℝ)^gamma ≤ root := by simpa [root] using (Nat.lt_floor_add_one ((scale : ℝ)^gamma)).le
  have hfac : ((2 * labels) ^ (7 ^ degree * (growth * height)) : ℕ) ≤ (scale : ℝ)^exp := by
    have hnat : ((2 * labels) ^ (growth * rate)) ^ height ≤ scale := Nat.pow_le_pow_left hw _
    have hreal := Real.rpow_le_rpow (by positivity) (Nat.cast_le.mpr hnat : (_ : ℝ) ≤ scale)
      (show 0 ≤ exp by unfold exp; positivity)
    have eqn : (growth * rate * height : ℕ) * exp = (7 ^ degree * (growth * height) : ℕ) := by
      unfold exp
      push_cast
      field_simp
    rw [← pow_mul, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), eqn,
      Real.rpow_natCast, ← Nat.cast_pow] at hreal
    exact hreal
  have hpow : (2 * labels) ^ (7 ^ degree * span) ≤ root := by
    apply (Nat.cast_le (α := ℝ)).mp
    unfold span
    rw [mul_add, pow_add, Nat.cast_mul, mul_comm]
    exact (mul_le_mul_of_nonneg_left hfac (by positivity)).trans (hdom.trans hroot)
  exact supply_of_schedules bank (by positivity) hl (Nat.cast_le.mp (hlarge.trans hroot))
    hpow (fun idx hi => htr idx hi root) hsch

theorem finiteScale_of_scheduler (scheduler : SchedulerTheorem) : FiniteScale :=
  finiteScale_of_supplies (supplies_of_scheduler scheduler)

theorem main_of_scheduler (scheduler : SchedulerTheorem) : MainTheorem :=
  main_of_crossing (finiteScale_of_scheduler scheduler)

theorem excess_of_scheduler (scheduler : SchedulerTheorem) : ExcessTheorem :=
  excess_of_crossing (finiteScale_of_scheduler scheduler)

theorem not_polynomialHirsch_of_scheduler (scheduler : SchedulerTheorem) : ¬ PolynomialHirsch :=
  not_polynomialHirsch_of_main (main_of_scheduler scheduler)

end OAI.Geometry.Hirsch
