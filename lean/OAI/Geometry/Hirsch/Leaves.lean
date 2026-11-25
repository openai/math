import OAI.Geometry.Hirsch.Compatibility

noncomputable section

open Set Filter

namespace OAI.Geometry.Hirsch.Layer

open Forest

variable {I : Type} {B V N : ℕ} {ep : Episodes N}

structure Times (ep : Episodes N) (B : ℕ) where
  time : Probe N B → ℝ
  interior : ∀ t, time t ∈ Ioo (ep.left t.1) (ep.right t.1)
  injective : Function.Injective time

namespace Times

variable (times : Times ep B)

theorem unit (t : Probe N B) : times.time t ∈ Icc 0 1 :=
  ⟨((ep.positive _).trans (times.interior t).1).le,((times.interior t).2.trans (ep.interior _)).le⟩

theorem ordered {t s : Probe N B} (he : t.1 < s.1) : times.time t < times.time s :=
  ((times.interior t).2.trans (ep.ordered he)).trans (times.interior s).1

theorem exists_times (ep : Episodes N) (B : ℕ) : Nonempty (Times ep B) := by
  let step := fun i => (ep.right i - ep.left i) / (B+1 : ℝ)
  have hp : ∀ i, 0 < step i := fun i => div_pos (sub_pos.mpr (ep.width i)) (by positivity)
  let time := fun t : Probe N B => ep.left t.1 + step t.1 * (t.2.val + 1)
  have hh : ∀ t, time t ∈ Ioo (ep.left t.1) (ep.right t.1) := by
    rintro ⟨i,b⟩
    have hb : (b.val : ℝ) < B := Nat.cast_lt.mpr b.isLt
    have he : step i * (B+1 : ℝ) = ep.right i - ep.left i := div_mul_cancel₀ _ (by positivity)
    dsimp only [time]
    constructor <;> nlinarith [hp i,Nat.cast_nonneg (α := ℝ) b.val]
  refine ⟨⟨time,hh,?_⟩⟩
  rintro ⟨i,b⟩ ⟨j,d⟩ he
  have ht : i = j := by
    rcases lt_trichotomy i j with hl | heq | hl
    · exact (((hh (i,b)).2.trans (ep.ordered hl)).trans (hh (j,d)).1).ne he |>.elim
    · exact heq
    · exact (((hh (j,d)).2.trans (ep.ordered hl)).trans (hh (i,b)).1).ne' he |>.elim
  subst j
  have hv : (b.val : ℝ) = d.val := by
    dsimp only [time] at he
    exact add_right_cancel (mul_left_cancel₀ (hp i).ne' (add_left_cancel he))
  exact congrArg (Prod.mk i) (Fin.ext (Nat.cast_injective hv))

def group (L k : ℕ) (t : Probe N B) := t.1.val / L^k

def site (L k : ℕ) [NeZero L] (t : Probe N B) : Fin L := ⟨group L k t % L,Nat.mod_lt _ (NeZero.pos L)⟩

theorem link (L k : ℕ) [NeZero L] (t : Probe N B) :
    group L (k+1) t * L + (site L k t).val = group L k t := by
  simp only [site,group,pow_succ,← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' _ _

theorem group_ordered (L k : ℕ) {t s : Probe N B} (hl : group L k t < group L k s) :
    times.time t < times.time s :=
  times.ordered (lt_of_not_ge (fun hh => hl.not_ge (Nat.div_le_div_right hh)))

def carrier (L k : ℕ) : Carrier times.time (group L k) :=
  Classical.choice (Carrier.exists_of_order (fun _ _ => times.group_ordered L k))

def penalty (A : ℝ) (b : Fin B) (t : Probe N B) :=
  A * (times.time t - times.time (t.1,b))^2 - 1

theorem penalty_high : ∃ A > 0, ∀ b t, b ≠ t.2 → 1 < times.penalty A b t := by
  have ev : ∀ᶠ A : ℝ in atTop, ∀ b t, b ≠ t.2 → 1 < times.penalty A b t := by
    apply eventually_all.mpr; intro b
    apply eventually_all.mpr; intro t
    by_cases hn : b = t.2
    · simp [hn]
    have ht : times.time t ≠ times.time (t.1,b) := times.injective.ne (fun he => hn (congrArg Prod.snd he.symm))
    filter_upwards [eventually_big (b := 2) (sq_pos_of_ne_zero (sub_ne_zero.mpr ht))] with A ha _
    unfold penalty
    linarith
  exact ((eventually_gt_atTop 0).and ev).exists

theorem penalty_patch (L : ℕ) {R A : ℝ} (hr : 0 ≤ R) (ha : 0 ≤ A) (b : Fin B) :
    ∀ᶠ a : ℝ in atTop,
      Supported times.time (fun t => times.penalty A b t + (times.carrier L 0).lift a R t) := by
  have hs : ∀ t, ∃ f : Line, f (times.time t) = times.penalty A b t ∧
      ∀ s, group L 0 s = group L 0 t → f (times.time s) ≤ times.penalty A b s := by
    intro t
    let z := times.time (t.1,b)
    let f : Line := A • (tangent (times.time t) + ⟨-2*z,z^2⟩) + Line.const (-1)
    have he : ∀ y, f y = A*(tangent (times.time t) y - 2*z*y + z^2)-1 := by
      intro y
      simp only [f,Line.add_apply,Line.smul_apply,Line.const_apply]
      ring
    refine ⟨f,?_,fun s hh => ?_⟩
    · rw [he,tangent_self]; unfold penalty z; ring
    · have hn : s.1 = t.1 := Fin.ext (by simpa [group] using hh)
      rw [he,penalty,hn]
      change _ ≤ A*(times.time s - z)^2 - 1
      linarith [mul_le_mul_of_nonneg_left (tangent_le (times.time t) (times.time s)) ha]
  simpa only [one_mul] using (times.carrier L 0).patch hr one_pos _ hs

end Times

variable [NeZero N] [NeZero B]

def leafPanel {time : Probe N B → ℝ} {value : Fin B → Probe N B → ℝ}
    (hs : ∀ b, Supported time (value b)) (i : I) : Panel I B V i where
  Row := Probe N B × Index B V
  coeff r := LinearMap.proj (i,r.2)
  rhs r := r.2.1.elim (Line.const 0) (fun b => (hs b).line r.1)
  mono _ _ _ hh := hh _
  pos _ := one_pos
  individual role pos := ⟨((0,0),role,pos),rfl⟩
  localizes := by
    rintro ⟨_,_ | b,pos⟩
    · exact ⟨0,fun _ hh => (hh pos).1⟩
    · exact ⟨b,fun _ hh => (hh pos).2⟩

theorem leaf_panel {time : Probe N B → ℝ} {value : Fin B → Probe N B → ℝ}
    (hs : ∀ b, Supported time (value b)) (i : I) (t : Probe N B) (D : ℝ)
    (hl : value t.2 t < D) (hu : ∀ d ≠ t.2, 1+D < value d t) :
    (leafPanel (V := V) hs i).Leaf (time t) D t.2 := by
  intro x hx
  refine ⟨fun pos d hd => ?_,fun hp f r he => ?_⟩
  · apply lt_sub_iff_add_lt.mpr
    exact (hu d hd).trans_le (((hs d).touch t).symm.trans_le (hx (t,some d,pos)))
  · obtain ⟨s,_ | d,kind,l⟩ := r
    · cases kind <;> simp [leafPanel,impulse]
    · by_cases hd : d = t.2
      · subst d
        exact ((hp (kind,l)).not_gt (he.trans_le ((hs _).below s t) |>.trans_lt hl)).elim
      · simp [leafPanel,impulse,hd]

end OAI.Geometry.Hirsch.Layer
