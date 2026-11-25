import OAI.Geometry.Hirsch.Envelopes

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer

variable {T : Type} {time : T → ℝ} {block : T → ℕ}

namespace Carrier

variable (c : Carrier time block)

def val (t : T) := c.line (block t) (time t)

theorem support : Supported time c.val := by
  refine fun t => ⟨c.line (block t),rfl,fun s => ?_⟩
  by_cases he : block t = block s
  · rw [he]; rfl
  · exact (c.highest s _ he).le

def lift (scale bend : ℝ) (t : T) := scale * c.val t + bend*(time t)^2

theorem supported {a R : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ R) : Supported time (c.lift a R) :=
  (c.support.scale ha).add ((Supported.square time).scale hr)

def extend (a R w : ℝ) (t : T) (f : Line) :=
  f + w • (a • c.line (block t) + R • tangent (time t))

theorem extend_touch (a R w : ℝ) (t : T) (f : Line) :
    c.extend a R w t f (time t) = f (time t) + w*c.lift a R t := by
  simp [extend,lift,val]

theorem extend_le {a R w : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ R) (hw : 0 ≤ w) (t s : T) (f : Line) :
    c.extend a R w t f (time s) ≤ f (time s) + w*c.lift a R s := by
  simp only [extend,Line.add_apply,Line.smul_apply,lift,val]
  refine add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left ?_ ha) (mul_le_mul_of_nonneg_left ?_ hr)) hw) _
  · by_cases he : block t = block s
    · rw [he]
    · exact (c.highest s _ he).le
  · exact tangent_le ..

theorem extend_lt {R w : ℝ} (hr : 0 ≤ R) (hw : 0 < w) {t s : T} (hn : block t ≠ block s)
    (f : Line) (v : ℝ) :
    ∀ᶠ a : ℝ in atTop, c.extend a R w t f (time s) < v + w*c.lift a R s := by
  have hh := mul_pos hw (sub_pos.mpr (c.highest s _ hn))
  filter_upwards [eventually_big (b := f (time s)-v) hh] with a ha
  simp only [extend,Line.add_apply,Line.smul_apply,lift,val]
  linarith [mul_le_mul_of_nonneg_left (tangent_le (time t) (time s)) (mul_nonneg hw.le hr)]

theorem patch [Finite T] {R w : ℝ} (hr : 0 ≤ R) (hw : 0 < w) (value : T → ℝ)
    (hs : ∀ t, ∃ f : Line, f (time t) = value t ∧ ∀ s, block s = block t → f (time s) ≤ value s) :
    ∀ᶠ a : ℝ in atTop, Supported time (fun t => value t + w*c.lift a R t) := by
  apply eventually_all.mpr
  intro t
  obtain ⟨f,hf,hl⟩ := hs t
  have ev : ∀ᶠ a : ℝ in atTop, ∀ s, c.extend a R w t f (time s) ≤ value s + w*c.lift a R s := by
    apply eventually_all.mpr
    intro s
    by_cases he : block s = block t
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
      exact (c.extend_le ha hr hw.le t s f).trans (add_le_add_left (hl s he) _)
    · exact (c.extend_lt hr hw (Ne.symm he) f (value s)).mono (fun _ h => h.le)
  filter_upwards [ev] with a ha
  exact ⟨c.extend a R w t f,(c.extend_touch a R w t f).trans (by rw [hf]),ha⟩

end Carrier

structure Shift (time : T → ℝ) (block : T → ℕ) (size : ℝ) where
  carrier : Carrier time block
  scale : ℝ
  bend : ℝ
  scalePos : 0 < scale
  bendPos : 0 ≤ bend
  small : bend ≤ size/200

namespace Shift

variable {size : ℝ} (s : Shift time block size)

def val := s.carrier.lift s.scale s.bend

def line (n : ℕ) := s.scale • s.carrier.line n

theorem value (t : T) : s.val t = s.line (block t) (time t) + s.bend*(time t)^2 := by
  simp [val,Carrier.lift,Carrier.val,line]

theorem supported : Supported time s.val := s.carrier.supported s.scalePos.le s.bendPos

theorem zero (hz : s.bend = 0) (t : T) (ht : block t = 0) : s.val t = 0 := by
  simp [value,hz,ht,line,s.carrier.zero]

theorem perturb [Finite T] (hi : Function.Injective time) (hb : 0 < s.bend) (f : T → ℝ) :
    ∀ᶠ a in 𝓝 (0 : ℝ), Supported time (fun t => s.val t + a*f t) := by
  filter_upwards [perturb_square hi hb f] with a ha
  simpa only [val,Carrier.lift,add_assoc] using (s.carrier.support.scale s.scalePos.le).add ha

end Shift
end OAI.Geometry.Hirsch.Layer
