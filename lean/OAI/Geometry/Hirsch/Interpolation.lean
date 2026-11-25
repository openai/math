import OAI.Geometry.Hirsch.StateSequence

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer

variable {T : Type} [Fintype T] {L V K : ℕ} {code : Bundles L V}
  {time : T → ℝ} {block : T → ℕ} {site : T → Fin L}

def rank (time : T → ℝ) (t : T) : Fin (Fintype.card T + 1) :=
  ⟨{s | time s < time t}.ncard,by simpa using ncard_le_card {s | time s < time t}⟩

theorem rank_lt {s t : T} (h : time s < time t) : rank time s < rank time t := by
  apply ncard_lt_ncard _ (toFinite _)
  exact ssubset_iff_subset_ne.mpr ⟨fun _ hh => lt_trans hh h,fun he =>
    lt_irrefl (time s) (show s ∈ {x | time x < time s} from he.symm ▸ h)⟩

def layerIndex (time : T → ℝ) (site : T → Fin L) (t : T) := micro (site t) (rank time t)

theorem index_lt (ho : ∀ s t, block s = block t → site s < site t → time s < time t)
    {s t : T} (he : block s = block t) (hh : time s < time t) :
    layerIndex time site s < layerIndex time site t := by
  rcases lt_trichotomy (site s) (site t) with hl | hl | hl
  · exact micro_lt hl _ _
  · unfold layerIndex micro; rw [hl]; exact Nat.add_lt_add_left (rank_lt hh) _
  · exact (hh.not_gt (ho _ _ he.symm hl)).elim

theorem spacing (hi : Function.Injective time) :
    ∃ A M : ℝ, 0 < A ∧ 1 ≤ M ∧ ∀ s t, s ≠ t → 1 < A*|time s-time t| ∧ 1+A*|time s-time t| ≤ M := by
  have ev : ∀ᶠ A : ℝ in atTop, ∀ s t, s ≠ t → 1 < A*|time s-time t| := by
    apply eventually_all.mpr; intro s
    apply eventually_all.mpr; intro t
    by_cases he : s = t
    · simp [he]
    · exact (eventually_big (abs_pos.mpr (sub_ne_zero.mpr (hi.ne he)))).mono fun _ h _ => h
  obtain ⟨A,ha,hs⟩ := ((eventually_gt_atTop 0).and ev).exists
  obtain ⟨M,hm⟩ := Finite.bddAbove_range (fun p : T × T => 1+A*|time p.1-time p.2|)
  exact ⟨A,max 1 M,ha,le_max_left ..,fun s t hn =>
    ⟨hs s t hn,(hm (mem_range_self (s,t))).trans (le_max_right ..)⟩⟩

omit [Fintype T] in
theorem minorant {A M : ℝ} (hi : Function.Injective time)
    (hspace : ∀ s t, s ≠ t → 1 < A*|time s-time t| ∧ 1+A*|time s-time t| ≤ M)
    (t : T) (d : T → ℝ) (hd : ∀ s, 0 ≤ d s)
    (hboth : ∀ s u, block s = block t → block u = block t → time s < time t → time t < time u →
      M < d s ∨ M < d u) :
    ∃ f : Line, f (time t) = 1 ∧ ∀ s, block s = block t → s ≠ t → f (time s) < d s := by
  by_cases hl : ∀ s, block s = block t → time s < time t → M < d s
  · refine ⟨⟨-A,1+A*time t⟩,by dsimp; ring,fun s hs hn => ?_⟩
    have hh := hspace s t hn
    change -A*time s+(1+A*time t) < _
    rcases lt_or_gt_of_ne (hi.ne hn) with h | h
    · rw [abs_of_neg (sub_neg.mpr h)] at hh
      linarith [hl s hs h,hh.2]
    · rw [abs_of_pos (sub_pos.mpr h)] at hh
      linarith [hd s,hh.1]
  · push Not at hl
    obtain ⟨u,hu,hlt,hlo⟩ := hl
    refine ⟨⟨A,1-A*time t⟩,by dsimp; ring,fun s hs hn => ?_⟩
    have hh := hspace s t hn
    change A*time s+(1-A*time t) < _
    rcases lt_or_gt_of_ne (hi.ne hn) with h | h
    · rw [abs_of_neg (sub_neg.mpr h)] at hh
      linarith [hd s,hh.1]
    · rw [abs_of_pos (sub_pos.mpr h)] at hh
      linarith [(hboth u s hu hs hlt h).resolve_left hlo.not_gt,hh.2]

theorem interpolation (input : ∀ k, 0 < k → Nonempty (StateSequence code K k (1/4))) :
    Interpolates code (costRows V K) := by
  intro T inst time block site hi ho
  obtain ⟨A,M,_,hm,hs⟩ := spacing hi
  have ht : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n,hn,hq⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (ht.eventually (eventually_small (a := 2*M) one_pos))).exists
  let q := (1/4 : ℝ)^n
  have hp : 0 < q := by unfold q; positivity
  have hl : 2*q*M < 1 := by unfold q; linarith
  have hh : q < 1/2 := by nlinarith
  obtain ⟨raw⟩ := input (Fintype.card T + 1) (by omega)
  obtain ⟨seq⟩ := raw.power n hn.ne'
  let idx := layerIndex time site
  choose cuts hc he hw using fun t => upper_cuts (seq.states (idx t))
    (seq.inhabited _) (seq.count _) (seq.nonneg _)
  refine ⟨⟨cuts,hc,hw,?_,?_⟩⟩
  · intro t y hy
    rw [he] at hy
    exact seq.identifies _ _ _ (upper_vertex hy)
  · intro t c hc
    let d := fun s => seq.minVal c (idx s)
    have hnon := (hw _ _ hc).1
    have hone : 1 ≤ d t := by
      obtain ⟨x,hx,hm⟩ := seq.min_attained c (idx t)
      have hv : x ∈ (region (cuts t)).body := (he t).symm ▸ upper_mem hx
      exact ((mem_region.mp hv).2 c hc).trans_eq hm.symm
    have hboth : ∀ s u, block s = block t → block u = block t → time s < time t → time t < time u →
        M < d s ∨ M < d u := by
      intro s u hs hu h₁ h₂
      have he : d t ≤ 2*q*max (d s) (d u) := seq.min_middle hnon hp.le hh
        (index_lt ho hs h₁) (index_lt ho hu.symm h₂) (micro_bound _ _)
      by_contra! hn
      exact hl.not_ge (hone.trans (he.trans (mul_le_mul_of_nonneg_left (max_le hn.1 hn.2) (by positivity))))
    obtain ⟨f,hf,hgap⟩ := minorant hi hs t d (fun _ => seq.min_nonneg hnon _) hboth
    refine ⟨f,hf,fun s hs hn => ⟨d s,hgap s hs hn,fun w hmem => ?_⟩⟩
    rw [he] at hmem
    exact upper_bound hnon (fun _ hx => seq.min_le c hx) hmem

theorem layers_of_numerical (input : NumericalLayers) : LayerTheorem := by
  intro rate
  obtain ⟨L,V,K,hL,hV,hr,code,hs⟩ := input rate
  exact ⟨L,V,costRows V K,hL,hV,hr,code,interpolation hs⟩

end OAI.Geometry.Hirsch.Layer

namespace OAI.Geometry.Hirsch

theorem main_of_numerical (input : Layer.NumericalLayers) : MainTheorem :=
  main_of_scheduler (Layer.scheduler_of_layers (Layer.layers_of_numerical input))

theorem excess_of_numerical (input : Layer.NumericalLayers) : ExcessTheorem :=
  excess_of_scheduler (Layer.scheduler_of_layers (Layer.layers_of_numerical input))

theorem not_polynomialHirsch_of_numerical (input : Layer.NumericalLayers) : ¬ PolynomialHirsch :=
  not_polynomialHirsch_of_main (main_of_numerical input)

end OAI.Geometry.Hirsch
