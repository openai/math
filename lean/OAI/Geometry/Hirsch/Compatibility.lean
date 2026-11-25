import OAI.Geometry.Hirsch.Parameters

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer

theorem Supported.congr {T : Type} {time f g : T → ℝ} (hs : Supported time f)
    (he : ∀ t, f t = g t) : Supported time g := funext he ▸ hs

variable {N B L V C : ℕ} {code : Bundles L V}
  {time : Probe N B → ℝ} {block : Probe N B → ℕ} {site : Probe N B → Fin L}
  {atlas : Atlas code time block site C}

structure Setup.Compatible (cfg : Setup atlas) : Prop where
  price : Supported time (fun t => -cfg.g t)
  first : ∀ d, Supported time (fun t => -cfg.g t - if d = t.2 then 1 else 0)
  second : ∀ d, Supported time (fun t => cfg.child t + if d = t.2 then -cfg.lam else cfg.lam)
  offset : ∀ s t, ∃ f : Line, ∀ u, block u = block t → cfg.offset u s = f (time u)

namespace Setup.Result

variable {cfg : Setup atlas} (res : cfg.Result) (c : Carrier time block) {R : ℝ}

theorem ordinary (hg : cfg.Compatible) (hr : 0 ≤ R) (r : Stencil code B) :
    ∀ᶠ a : ℝ in atTop, Supported time (fun t => bound (res.data t) (c.lift a R t) t.2 r) := by
  have hd : ∀ᶠ a : ℝ in atTop, Supported time (c.lift a R) :=
    (eventually_ge_atTop 0).mono fun _ ha => c.supported ha hr
  let par := res.par
  rcases r with ⟨_ | d,_ | _,l⟩ | l | e
  · filter_upwards [hd] with a ha
    exact (ha.scale (a := 1/2) (by norm_num)).congr (fun _ => by simp [bound]; ring)
  · filter_upwards [hd] with a ha
    have h₁ := (ha.scale (a := 1/2) (by norm_num)).add (hg.price.scale par.sigpos.le)
    apply (h₁.add (Supported.const time (-3*par.mu))).congr
    intro t
    simp only [bound,res.shift,par]
    ring
  · filter_upwards [hd] with a ha
    have h₁ := (ha.scale (a := 1/2) (by norm_num)).add ((hg.first d).scale par.sigpos.le)
    apply h₁.congr
    intro t
    simp only [bound,res.shift,par]
    split <;> ring
  · apply Eventually.of_forall
    intro a
    apply ((hg.second d).scale par.epos.le).congr
    intro t
    simp only [bound,res.child,res.lam,par]
  · filter_upwards [hd] with a ha
    exact ha.add (Supported.const time (-(par.K*par.eps)))
  · have ev : ∀ᶠ a : ℝ in atTop,
        Supported time (fun t => par.eps * cfg.offset t e.1 + 1*c.lift a R t) := by
      apply c.patch hr one_pos
      intro t
      obtain ⟨f,hf⟩ := hg.offset e.1 t
      exact ⟨par.eps • f,by simp [hf t rfl],fun s hs => by simp [hf s hs]⟩
    filter_upwards [ev] with a ha
    apply (ha.scale (code.bid_pos par.qpos e).le).congr
    intro t
    simp only [bound,res.offset,par]
    ring

theorem plate (hg : cfg.Compatible) (hr : 0 ≤ R) :
    ∀ᶠ a : ℝ in atTop, Plate time res.par res.data (c.lift a R) C := by
  have ho := eventually_all.mpr (res.ordinary c hg hr)
  have hc : ∀ᶠ a : ℝ in atTop, ∀ t (v : ↥(res.data t).cuts) (mask : Fin V → Bool),
      let D := c.lift a R
      let w := replace res.par.M v.val mask
      ∃ line : Line, line (time t) = 1 + (D t/2 + (res.data t).shift) * dot w 1 ∧
        ∀ s ≠ t, ∀ y : Values V, (∀ l, D s/2 ≤ y l) →
          Expanded (res.data s).cuts res.par.M (adjusted (res.data s) (D s) y) → line (time s) < dot w y := by
    apply eventually_all.mpr; intro t
    apply eventually_all.mpr; intro v
    apply eventually_all.mpr; intro m
    have hv : v.val ∈ atlas.cuts t := (res.cuts t) ▸ v.property
    obtain ⟨f,hf,hl⟩ := res.ready t v.val hv m
    obtain ⟨hn,hp⟩ := atlas.weights t _ hv
    apply coarse_patch c R hr res.data t v.val hn hp ((res.data t).bounded _ v.property) m f
    · rw [res.shift]; exact hf
    · intro s hs hn w hw
      rw [res.cuts s] at hw
      exact hl s hs hn w hw
  filter_upwards [ho,hc] with a h₁ h₂
  refine ⟨fun t => ?_,fun t => ?_,h₁,fun t v hv => h₂ t ⟨v,hv⟩⟩
  · rw [res.cuts]; exact atlas.count t
  · rw [res.cuts]; exact atlas.weights t

end Setup.Result

theorem compatible (atlas : Atlas code time block site C)
    (hi : Function.Injective time) (ht : ∀ t, time t ∈ Icc 0 1)
    {prev : Probe N B → ℕ} (link : ∀ t, block t * L + (site t).val = prev t)
    {size : ℝ} (hp : 0 < size) (shift : Shift time prev size) (hb : 0 < shift.bend) :
    ∃ cfg : Setup atlas, cfg.Compatible ∧ cfg.child = shift.val ∧ 10*cfg.delta < size := by
  let delta := size/20
  have hd : 0 < delta := by unfold delta; linarith
  let sign := fun (d : Fin B) (t : Probe N B) => if d = t.2 then (-1 : ℝ) else 1
  have ev := eventually_all.mpr (fun d => shift.perturb hi hb (sign d))
  obtain ⟨lam,hl,hlow,hsec⟩ := small_positive ((eventually_le_nhds (by linarith : 0 < delta/4)).and ev)
  let ind := fun (d : Fin B) (t : Probe N B) => if d = t.2 then (-1 : ℝ) else 0
  obtain ⟨A,hA,hfirst⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (eventually_all.mpr (fun d => big_square hi (ind d)))).exists
  let g := fun t => A*(1-(time t)^2)
  have small : ∀ t, (time t)^2 ≤ 1 := fun t => by nlinarith [(ht t).1,(ht t).2]
  let offset := fun t (s : Fin L) => -(shift.line (block t*L+s.val) (time t)) - delta
  let cfg : Setup atlas := {
    child := shift.val, offset := offset, delta := delta, lam := lam, g := g, pos := hl, small := hlow,
    nonneg := fun t => mul_nonneg hA.le (sub_nonneg.mpr (small t)),
    current := fun t => by
      unfold offset
      rw [link,shift.value]
      have h₁ := mul_le_mul_of_nonneg_left (small t) hb.le
      have h₂ := mul_nonneg hb.le (sq_nonneg (time t))
      unfold delta
      constructor <;> linarith [shift.small] }
  refine ⟨cfg,⟨?_,?_,?_,?_⟩,rfl,by change 10*(size/20) < size; linarith⟩
  · apply (((Supported.square time).scale hA.le).add (Supported.const time (-A))).congr
    intro t; dsimp only [cfg,g]; ring
  · intro d; apply (hfirst d).congr
    intro t; dsimp only [cfg,g,ind]; split <;> ring
  · intro d; apply (hsec d).congr
    intro t; dsimp only [cfg,sign]; split <;> ring
  · intro s t
    refine ⟨(-1 : ℝ) • shift.line (block t*L+s.val) + Line.const (-delta),fun u hu => ?_⟩
    simp [cfg,offset,hu,sub_eq_add_neg]

end OAI.Geometry.Hirsch.Layer
