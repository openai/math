import OAI.Geometry.Hirsch.UpperHull

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {V : ℕ}

def normalized (rows : Finset (Halfspace V)) : Finset (Values V) :=
  (rows.filter (fun r => 0 < r.2)).image (fun r => r.2⁻¹ • r.1)

theorem norm_iff (r : Halfspace V) (hr : 0 < r.2) (x : Values V) :
    1 ≤ dot (r.2⁻¹ • r.1) x ↔ r.2 ≤ dot r.1 x := by
  rw [dot_scale,inv_mul_eq_div,le_div_iff₀ hr,one_mul]

theorem dot_one_pos {c : Values V} (hn : 0 ≤ c) (hc : c ≠ 0) : 0 < dot c 1 := by
  have hex : ∃ l, 0 < c l := by
    by_contra! hh
    exact hc (le_antisymm hh hn)
  obtain ⟨l,hl⟩ := hex
  simp only [dot,LinearMap.coe_mk,AddHom.coe_mk,Pi.one_apply,mul_one]
  exact Finset.sum_pos' (fun j _ => hn j) ⟨l,Finset.mem_univ _,hl⟩

theorem Models.normalized {rows : Finset (Halfspace V)} {s : Finset (Values V)} (model : Models rows s)
    (hs : s.Nonempty) :
    (region (normalized rows)).body = upperHull s ∧
      ∀ c ∈ normalized rows, 0 ≤ c ∧ 0 < dot c 1 := by
  have he : (region (Layer.normalized rows)).body = above rows := by
    ext x
    rw [mem_region]
    constructor
    · intro hh r hr
      by_cases hp : 0 < r.2
      · apply (norm_iff r hp x).mp
        exact hh.2 _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hr,hp⟩))
      · have hle := dot_mono (model.nonneg r hr) (show 0 ≤ x from hh.1)
        rw [map_zero] at hle
        exact (le_of_not_gt hp).trans hle
    · intro hx
      refine ⟨fun l => ?_,fun c hc => ?_⟩
      · simpa using hx _ (model.proj (axis_mem l))
      · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hr,hp⟩ := Finset.mem_filter.mp hr
        exact (norm_iff r hp x).mpr (hx r hr)
  refine ⟨he.trans model.body,fun c hc => ?_⟩
  have hn : 0 ≤ c := by
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hr,hp⟩ := Finset.mem_filter.mp hr
    exact fun l => mul_nonneg (inv_nonneg.mpr hp.le) (model.nonneg _ hr l)
  refine ⟨hn,dot_one_pos hn (fun hz => ?_)⟩
  obtain ⟨x,hx⟩ := hs
  have hh := (mem_region.mp ((he.trans model.body).symm ▸ upper_mem hx)).2 c hc
  rw [hz,dot_zero] at hh
  linarith

theorem upper_cuts (s : Finset (Values V)) {K : ℕ} (hn : s.Nonempty) (hh : s.card ≤ K)
    (hs : ∀ v ∈ s, 0 ≤ v) :
    ∃ cuts : Finset (Values V), cuts.card ≤ costRows V K ∧
      (region cuts).body = upperHull s ∧ ∀ c ∈ cuts, 0 ≤ c ∧ 0 < dot c 1 := by
  obtain ⟨rows,hm,hb⟩ := upper_model s hs
  refine ⟨normalized rows,?_,hm.normalized hn⟩
  exact Finset.card_image_le.trans ((Finset.card_filter_le ..).trans (hb.trans (costRows_mono _ hh)))

end OAI.Geometry.Hirsch.Layer
