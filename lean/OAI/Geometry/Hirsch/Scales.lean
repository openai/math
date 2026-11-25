import OAI.Geometry.Hirsch.Budgets

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch

def Supplies : Prop :=
  ∀ degree depth : ℕ, ∀ gamma : ℝ, 0 < gamma →
    ∃ base : ℕ, 2 ≤ base ∧ ∀ᶠ height : ℕ in atTop,
      let scale := base ^ height
      Nonempty (Supply degree scale depth (⌊(scale : ℝ)^gamma⌋₊ + 1))

theorem Supply.seed {degree scale depth mult : ℕ} {gamma eta : ℝ}
    (supply : Supply degree scale depth (⌊(scale : ℝ)^gamma⌋₊ + 1))
    (hd : 2 ≤ degree) (hs : 2 ≤ scale) (hm : 1 ≤ mult) (hbig : 4 ≤ (scale : ℝ)^gamma)
    (hdepth : degree ≤ gamma * exponent depth degree * depth)
    (hbudget : 2 * gamma * exponent depth degree * (33 * degree + 1 : ℕ) ≤ eta)
    (episodes : Episodes scale) : CrossingSeed degree scale mult eta gamma episodes := by
  let root := ⌊(scale : ℝ)^gamma⌋₊ + 1
  let windows := volume root depth degree
  have hs' : (1 : ℝ) ≤ scale := by exact_mod_cast (show 1 ≤ scale by omega)
  have hp : (0 : ℝ) < scale := by positivity
  have hl : (scale : ℝ)^gamma ≤ root := by simpa [root] using (Nat.lt_floor_add_one ((scale : ℝ)^gamma)).le
  have hr : 4 ≤ root := by exact_mod_cast hbig.trans hl
  have hw : 4 ≤ windows := hr.trans (Nat.le_self_pow (exponent_pos depth degree).ne' root)
  have hu : (root : ℝ) ≤ (scale : ℝ)^(2 * gamma) := by
    have he := Nat.floor_le (show 0 ≤ (scale : ℝ)^gamma by positivity)
    rw [two_mul, Real.rpow_add hp]
    simp only [root, Nat.cast_add, Nat.cast_one]
    nlinarith
  have heq : ∀ (exp : ℝ) (power : ℕ),
      (scale : ℝ)^(exp * exponent depth degree * power) =
        (((scale : ℝ)^exp)^(exponent depth degree))^power := by
    intro exp power
    rw [Real.rpow_mul hp.le, Real.rpow_mul hp.le, Real.rpow_natCast, Real.rpow_natCast]
  have hdeep : scale ^ degree ≤ windows ^ depth := by
    have hh := Real.rpow_le_rpow_of_exponent_le hs' hdepth
    rw [Real.rpow_natCast, heq] at hh
    apply (Nat.cast_le (α := ℝ)).mp
    simp only [windows, volume, Nat.cast_pow]
    exact hh.trans (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl _) _)
  let overhead := windows ^ (33 * degree + 1)
  have hov : (overhead : ℝ) ≤ (scale : ℝ)^eta := by
    have hh := Real.rpow_le_rpow_of_exponent_le hs' hbudget
    rw [heq] at hh
    simp only [overhead, windows, volume, Nat.cast_pow]
    exact (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hu _) _).trans hh
  have hsize : volume root depth (degree - 1) + 1 ≤ overhead := by
    have hv : volume root depth (degree - 1) ≤ windows := volume_mono (by omega) _ (by omega)
    have hw' : windows ^ 2 ≤ overhead := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  let rows := rowBudget windows mult scale (degree - 1)
  have hrow : rows + 3 ≤ overhead * (mult * scale) := by
    have hh : 0 < rows := by unfold rows rowBudget; positivity
    have he : overhead * (mult * scale) = windows * rows := by
      unfold overhead rows rowBudget
      rw [Nat.sub_add_cancel (by omega : 1 ≤ degree), pow_succ', mul_assoc]
    rw [he]
    nlinarith
  have hr' : (rows + 3 : ℕ) ≤ mult * (scale : ℝ) ^ (1 + eta) := by
    rw [Real.rpow_add hp, Real.rpow_one]
    calc
      _ ≤ ((overhead * (mult * scale) : ℕ) : ℝ) := Nat.cast_le.mpr hrow
      _ = mult * ((scale : ℝ) * overhead) := by push_cast; ring
      _ ≤ _ := by gcongr
  exact (supply.iterate hr hs hm hdeep (degree - 1) 0 (by omega)).seed (by omega)
    ((Nat.cast_le.mpr hsize).trans hov) hr' episodes

theorem finiteScale_of_supplies (supply : Supplies) : FiniteScale := by
  intro degree hd eta he _
  obtain ⟨den, hden⟩ := exists_nat_gt (2 * (33 * degree + 1 : ℕ) / eta)
  have hpos : (0 : ℝ) < den := lt_of_le_of_lt (by positivity) hden
  let depth := degree * den
  let gamma := 1 / ((den : ℝ) * exponent depth degree)
  have hx : (0 : ℝ) < exponent depth degree := by exact_mod_cast exponent_pos depth degree
  have hg : 0 < gamma := by unfold gamma; positivity
  have hh : gamma * exponent depth degree = 1 / (den : ℝ) := by
    unfold gamma
    field_simp
  have hdeep : (degree : ℝ) ≤ gamma * exponent depth degree * depth := by
    rw [hh, show (depth : ℝ) = degree * den by simp [depth]]
    field_simp
    exact le_rfl
  have hbudget : 2 * gamma * exponent depth degree * (33 * degree + 1 : ℕ) ≤ eta := by
    rw [mul_assoc 2 gamma, hh]
    have := (div_lt_iff₀ he).mp hden
    apply le_of_lt
    rw [show 2 * (1 / (den : ℝ)) * (33 * degree + 1 : ℕ) = 2 * (33 * degree + 1 : ℕ) / den by ring]
    exact (div_lt_iff₀ hpos).mpr (by linarith)
  obtain ⟨base, hb, hs⟩ := supply degree depth gamma hg
  have ht : Tendsto (fun height : ℕ => base ^ height) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  refine ⟨base, hb, gamma, hg, ?_⟩
  filter_upwards [hs, ht.eventually (eventually_ge_atTop 2),
    ht.eventually (eventually_power hg 4)] with height hsup hscale hbig mult hm episodes
  exact hsup.some.seed hd hscale hm hbig hdeep hbudget episodes

end OAI.Geometry.Hirsch
