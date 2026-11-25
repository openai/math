import OAI.Geometry.Hirsch.Carriers

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer

variable {T : Type} {L V C : ℕ} {code : Bundles L V}
  {time : T → ℝ} {block : T → ℕ} {site : T → Fin L}

structure Atlas (code : Bundles L V) (time : T → ℝ) (block : T → ℕ) (site : T → Fin L) (C : ℕ) where
  cuts : T → Finset (Values V)
  count : ∀ t, (cuts t).card ≤ C
  weights : ∀ t c, c ∈ cuts t → 0 ≤ c ∧ 0 < dot c 1
  identifies : ∀ t y, y ∈ (region (cuts t)).body.extremePoints ℝ → code.Identifies (site t) y
  minorant : ∀ t c, c ∈ cuts t → ∃ f : Line, f (time t) = 1 ∧
    ∀ s, block s = block t → s ≠ t → ∃ d, f (time s) < d ∧ ∀ w ∈ (region (cuts s)).body, d ≤ dot c w

namespace Atlas

variable (atlas : Atlas code time block site C)

def Ready (M sigma : ℝ) (g : T → ℝ) : Prop :=
  ∀ t c, c ∈ atlas.cuts t → ∀ mask,
    let v := replace M c mask
    ∃ f : Line, f (time t) = 1 + (sigma * g t) * dot v 1 ∧
      ∀ s, block s = block t → s ≠ t → ∀ w ∈ (region (atlas.cuts s)).body, f (time s) < dot c w

theorem ready [Finite T] (M : ℝ) (g : T → ℝ) : ∀ᶠ sigma in 𝓝 (0 : ℝ), atlas.Ready M sigma g := by
  have ev : ∀ᶠ sigma in 𝓝 (0 : ℝ), ∀ t (c : ↥(atlas.cuts t)) (mask : Fin V → Bool),
      ∃ f : Line, f (time t) = 1 + (sigma*g t)*dot (replace M c.val mask) 1 ∧
        ∀ s, block s = block t → s ≠ t → ∀ w ∈ (region (atlas.cuts s)).body, f (time s) < dot c.val w := by
    apply eventually_all.mpr; intro t
    apply eventually_all.mpr; intro c
    apply eventually_all.mpr; intro mask
    obtain ⟨f,hf,hl⟩ := atlas.minorant t _ c.property
    let a := dot (replace M c.val mask) 1
    have hh : ∀ᶠ sigma in 𝓝 (0 : ℝ), ∀ s, block s = block t → s ≠ t →
        ∀ w ∈ (region (atlas.cuts s)).body, f (time s) + sigma*g t*a < dot c.val w := by
      apply eventually_all.mpr; intro s
      by_cases he : block s = block t ∧ s ≠ t
      · obtain ⟨d,hd,hw⟩ := hl s he.1 he.2
        filter_upwards [eventually_small (a := g t*a) (sub_pos.mpr hd)] with sigma hs _ _ w hv
        linarith [hw w hv]
      · exact Eventually.of_forall (fun _ h₁ h₂ => (he ⟨h₁,h₂⟩).elim)
    filter_upwards [hh] with sigma hs
    refine ⟨f + Line.const (sigma*g t*a),?_,?_⟩
    · simp only [Line.add_apply,Line.const_apply,hf,a]
    · simpa only [Line.add_apply,Line.const_apply] using hs
  exact ev.mono (fun _ hh t c hc => hh t ⟨c,hc⟩)

theorem bounded [Finite T] : ∃ M > 0, ∀ t c, c ∈ atlas.cuts t → ∀ l, c l ≤ M := by
  let f := fun a : Σ t, ↥(atlas.cuts t) × Fin V => a.2.1.val a.2.2
  obtain ⟨K,hK⟩ := Finite.bddAbove_range f
  exact ⟨max 1 K,one_pos.trans_le (le_max_left ..),fun t c hc l =>
    (hK (mem_range_self ⟨t,⟨c,hc⟩,l⟩)).trans (le_max_right ..)⟩

end Atlas

theorem coarse_lower {par : Parameters code} (data : SampleData par) {D : ℝ} {w c v : Values V}
    (hc : 0 ≤ c) (hcv : c ≤ v) (hw : ∀ l, D/2 ≤ w l) :
    dot c (scaled par.M (adjusted data D w)) + dot v 1 / 2 * D ≤ dot v w := by
  let z := adjusted data D w
  let y := scaled par.M z
  let u := w - (D/2) • 1
  have hy : 0 ≤ y := scaled_nonneg par.Mpos.le z
  have hu : y ≤ u := by
    intro l
    have hh : y l ≤ max (z l) 0 := by
      rw [← scaled_eq par.Mpos.le]
      exact le_mul_of_one_le_right (hy l) (dilation_one par.Mpos.le z)
    refine hh.trans (max_le ?_ ?_)
    · simp only [u,z,adjusted,Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
      linarith [data.shiftPos]
    · simpa [u] using hw l
  have hle := (dot_weights hcv hy).trans (dot_mono (hc.trans hcv) hu)
  unfold u at hle
  rw [map_sub,map_smul,smul_eq_mul] at hle
  change dot c y + _ ≤ _
  linarith

theorem coarse_patch [Finite T] (carrier : Carrier time block) (R : ℝ) (hr : 0 ≤ R)
    {par : Parameters code} (data : T → SampleData par) (t : T) (c : Values V)
    (hc : 0 ≤ c) (hp : 0 < dot c 1) (hm : ∀ l, c l ≤ par.M) (mask : Fin V → Bool)
    (f : Line) (hf : f (time t) = 1 + (data t).shift * dot (replace par.M c mask) 1)
    (hgap : ∀ s, block s = block t → s ≠ t → ∀ w ∈ (region (data s).cuts).body, f (time s) < dot c w) :
    ∀ᶠ a : ℝ in atTop,
      let D := carrier.lift a R
      let v := replace par.M c mask
      ∃ line : Line, line (time t) = 1 + (D t/2 + (data t).shift) * dot v 1 ∧
        ∀ s ≠ t, ∀ w : Values V, (∀ l, D s/2 ≤ w l) →
          Expanded (data s).cuts par.M (adjusted (data s) (D s) w) → line (time s) < dot v w := by
  let v := replace par.M c mask
  let k := dot v 1 / 2
  have hcv : c ≤ v := replace_le hm mask
  have hk : 0 < k := half_pos (hp.trans_le (dot_weights hcv zero_le_one))
  have ev : ∀ᶠ a : ℝ in atTop, ∀ s, block s ≠ block t →
      carrier.extend a R k t f (time s) < 0 + k * carrier.lift a R s := by
    apply eventually_all.mpr; intro s
    by_cases he : block s = block t
    · simp [he]
    · exact (carrier.extend_lt hr hk (Ne.symm he) f 0).mono fun _ hh _ => hh
  filter_upwards [ev,eventually_ge_atTop (0 : ℝ)] with a ha hn
  refine ⟨carrier.extend a R k t f,?_,fun s hs w hw he => ?_⟩
  · calc
      _ = f (time t) + k * carrier.lift a R t := carrier.extend_touch ..
      _ = _ := by rw [hf]; unfold k v; ring
  · have hy := (expanded_iff par.Mpos.le (data s).bounded).mp he
    apply lt_of_lt_of_le _ (coarse_lower (data s) hc hcv hw)
    by_cases hb : block s = block t
    · exact (carrier.extend_le hn hr hk.le t s f).trans_lt (add_lt_add_left (hgap s hb hs _ hy) _)
    · have hz := dot_mono hc (show 0 ≤ scaled par.M _ from (mem_region.mp hy).1)
      rw [map_zero] at hz
      exact (ha s hb).trans_le (add_le_add_left hz _)

end OAI.Geometry.Hirsch.Layer
