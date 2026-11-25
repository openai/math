import OAI.Geometry.Hirsch.Plate

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer

variable {T : Type} {time : T → ℝ}

def tangent (x : ℝ) : Line := ⟨2*x,-x^2⟩

@[simp] theorem tangent_self (x : ℝ) : tangent x x = x^2 := by change 2*x*x+-x^2 = _; ring

theorem tangent_le (x y : ℝ) : tangent x y ≤ y^2 := by
  change 2*x*y+-x^2 ≤ _
  nlinarith [sq_nonneg (y-x)]

theorem tangent_lt {x y : ℝ} (hn : x ≠ y) : tangent x y < y^2 := by
  change 2*x*y+-x^2 < _
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hn)]

namespace Supported

theorem const (time : T → ℝ) (a : ℝ) : Supported time (fun _ => a) :=
  fun _ => ⟨Line.const a,Line.const_apply ..,fun _ => (Line.const_apply ..).le⟩

theorem add {f g : T → ℝ} (hf : Supported time f) (hg : Supported time g) :
    Supported time (fun t => f t + g t) := by
  intro t
  refine ⟨hf.line t + hg.line t,by simp [touch],fun s => ?_⟩
  simpa using add_le_add (hf.below t s) (hg.below t s)

theorem scale {f : T → ℝ} (hf : Supported time f) {a : ℝ} (ha : 0 ≤ a) :
    Supported time (fun t => a * f t) := by
  intro t
  refine ⟨a • hf.line t,by simp [touch],fun s => ?_⟩
  simpa using mul_le_mul_of_nonneg_left (hf.below t s) ha

theorem square (time : T → ℝ) : Supported time (fun t => (time t)^2) :=
  fun t => ⟨tangent (time t),tangent_self _,fun s => tangent_le _ (time s)⟩

end Supported

theorem small_positive {p : ℝ → Prop} (hp : ∀ᶠ x in 𝓝 (0 : ℝ), p x) : ∃ x > 0, p x := by
  obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨r/2,half_pos hr,hh (by rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)]; linarith)⟩

theorem eventually_small {a b : ℝ} (hb : 0 < b) : ∀ᶠ x in 𝓝 (0 : ℝ), x*a < b := by
  exact (continuous_id.mul continuous_const).continuousAt.eventually_lt continuous_const.continuousAt
    (by simpa using hb)

theorem eventually_big {a b : ℝ} (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, b < x*a :=
  (eventually_gt_atTop (b/a)).mono fun _ hh => (div_lt_iff₀ ha).mp hh

theorem perturb_square [Finite T] (hi : Function.Injective time) {R : ℝ} (hr : 0 < R) (f : T → ℝ) :
    ∀ᶠ a in 𝓝 (0 : ℝ), Supported time (fun t => R*(time t)^2 + a*f t) := by
  have ev : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ t s, a*(f t - f s) ≤ R*((time s)^2 - tangent (time t) (time s)) := by
    apply eventually_all.mpr; intro t
    apply eventually_all.mpr; intro s
    by_cases hn : t = s
    · subst s; simp
    · exact (eventually_small (mul_pos hr (sub_pos.mpr (tangent_lt (hi.ne hn))))).mono fun _ h => h.le
  filter_upwards [ev] with a ha t
  refine ⟨R • tangent (time t) + Line.const (a*f t),by simp,fun s => ?_⟩
  simp only [Line.add_apply,Line.smul_apply,Line.const_apply]
  linarith [ha t s]

theorem big_square [Finite T] (hi : Function.Injective time) (f : T → ℝ) :
    ∀ᶠ a : ℝ in atTop, Supported time (fun t => a*((time t)^2-1) + f t) := by
  have ev : ∀ᶠ a : ℝ in atTop, ∀ t s, f t - f s ≤ a*((time s)^2 - tangent (time t) (time s)) := by
    apply eventually_all.mpr; intro t
    apply eventually_all.mpr; intro s
    by_cases hn : t = s
    · subst s; simp
    · exact (eventually_big (sub_pos.mpr (tangent_lt (hi.ne hn)))).mono fun _ h => h.le
  filter_upwards [ev] with a ha t
  refine ⟨a • tangent (time t) + Line.const (f t-a),by simp; ring,fun s => ?_⟩
  simp only [Line.add_apply,Line.smul_apply,Line.const_apply]
  linarith [ha t s]

structure Carrier (time : T → ℝ) (block : T → ℕ) where
  line : ℕ → Line
  zero : line 0 = Line.const 0
  highest : ∀ t j, j ≠ block t → line j (time t) < line (block t) (time t)

namespace Carrier

variable {block : T → ℕ}

def staircase (sep : ℕ → ℝ) : ℕ → Line
  | 0 => Line.const 0
  | n+1 => staircase sep n + ⟨1,-sep n⟩

theorem exists_of_order [Finite T] (ho : ∀ s t, block s < block t → time s < time t) :
    Nonempty (Carrier time block) := by
  classical
  have hs : ∀ j : ℕ, ∃ x : ℝ, (∀ t, block t ≤ j → time t < x) ∧ (∀ t, j < block t → x < time t) := by
    intro j
    let left := {t | block t ≤ j}
    let right := {t | j < block t}
    by_cases hl : left.Nonempty
    swap
    · obtain ⟨m,hm⟩ := Finite.bddBelow_range time
      exact ⟨m-1,fun t ht => (hl ⟨t,ht⟩).elim,fun t _ => by linarith [hm (mem_range_self t)]⟩
    by_cases hr : right.Nonempty
    swap
    · obtain ⟨m,hm⟩ := Finite.bddAbove_range time
      exact ⟨m+1,fun t _ => by linarith [hm (mem_range_self t)],fun t ht => (hr ⟨t,ht⟩).elim⟩
    obtain ⟨s,hs,hmax⟩ := left.toFinite.exists_maximalFor time left hl
    obtain ⟨t,ht,hmin⟩ := right.toFinite.exists_minimalFor time right hr
    obtain ⟨x,hx,hy⟩ := exists_between (ho s t (lt_of_le_of_lt hs ht))
    refine ⟨x,fun u hu => lt_of_le_of_lt ?_ hx,fun u hu => lt_of_lt_of_le hy ?_⟩
    · exact le_of_not_gt (fun hh => hh.not_ge (hmax hu hh.le))
    · exact le_of_not_gt (fun hh => hh.not_ge (hmin hu hh.le))
  choose sep hl hr using hs
  refine ⟨⟨staircase sep,rfl,fun t j hn => ?_⟩⟩
  let f := fun n => staircase sep n (time t)
  have step : ∀ n, f (n+1) = f n + time t - sep n := by
    intro n
    unfold f; rw [staircase,Line.add_apply]
    change _ + (1 * time t + -sep n) = _
    ring
  rcases lt_or_gt_of_ne hn with hh | hh
  · have inc : ∀ n, j < n → n ≤ block t → f j < f n := by
      intro n
      induction n with
      | zero => omega
      | succ n ih =>
        intro h₁ h₂
        have hu : f n < f (n+1) := by rw [step]; linarith [hr n t (by omega)]
        rcases Nat.eq_or_lt_of_le (by omega : j ≤ n) with rfl | hj
        · exact hu
        · exact (ih hj (by omega)).trans hu
    exact inc _ hh le_rfl
  · have dec : ∀ n, block t < n → f n < f (block t) := by
      intro n
      induction n with
      | zero => omega
      | succ n ih =>
        intro h₁
        have hu : f (n+1) < f n := by rw [step]; linarith [hl n t (by omega)]
        rcases Nat.eq_or_lt_of_le (by omega : block t ≤ n) with he | hj
        · exact he.symm ▸ hu
        · exact hu.trans (ih hj)
    exact dec _ hh

end Carrier
end OAI.Geometry.Hirsch.Layer
