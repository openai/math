import OAI.Geometry.Hirsch.Layers

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {V : ℕ}

abbrev Halfspace (V : ℕ) := Values V × ℝ

def above (rows : Finset (Halfspace V)) : Set (Values V) :=
  {x | ∀ r ∈ rows, r.2 ≤ dot r.1 x}

theorem dot_add (a b x : Values V) : dot (a+b) x = dot a x + dot b x := by
  simp [dot,add_mul,Finset.sum_add_distrib]

theorem dot_scale (a : ℝ) (c x : Values V) : dot (a • c) x = a * dot c x := by
  simp [dot,mul_assoc,Finset.mul_sum]

@[simp] theorem dot_single (l : Fin V) (x : Values V) : dot (Pi.single l 1) x = x l := by
  simp [dot,Pi.single_apply]

@[simp] theorem dot_zero (x : Values V) : dot 0 x = 0 := by simp [dot]

def mix (a b : ℝ) (r s : Halfspace V) : Halfspace V :=
  (a • r.1 + b • s.1, a*r.2 + b*s.2)

def residual (r : Halfspace V) (v : Values V) := dot r.1 v - r.2

theorem residual_mix (a b : ℝ) (r s : Halfspace V) (x : Values V) :
    residual (mix a b r s) x = a*residual r x + b*residual s x := by
  simp only [residual,mix,dot_add,dot_scale]
  ring

def joinRows (rows : Finset (Halfspace V)) (v : Values V) : Finset (Halfspace V) :=
  rows.image (fun r => (r.1,min r.2 (dot r.1 v))) ∪
    ((rows.filter (fun r => residual r v < 0)) ×ˢ (rows.filter (fun r => 0 < residual r v))).image
      (fun p => mix (residual p.2 v) (-residual p.1 v) p.1 p.2)

theorem join_size (rows : Finset (Halfspace V)) (v : Values V) :
    (joinRows rows v).card ≤ rows.card + rows.card^2 := by
  unfold joinRows
  apply (Finset.card_union_le ..).trans
  refine Nat.add_le_add Finset.card_image_le (Finset.card_image_le.trans ?_)
  rw [Finset.card_product,pow_two]
  exact Nat.mul_le_mul (Finset.card_filter_le ..) (Finset.card_filter_le ..)

theorem join_nonneg {rows : Finset (Halfspace V)} (v : Values V) (hn : ∀ r ∈ rows, 0 ≤ r.1) :
    ∀ r ∈ joinRows rows v, 0 ≤ r.1 := by
  simp only [joinRows,Finset.mem_union,Finset.mem_image,Finset.mem_product,Finset.mem_filter]
  rintro _ (⟨r,hr,rfl⟩ | ⟨⟨r,s⟩,⟨⟨hr,hneg⟩,⟨hs,hpos⟩⟩,rfl⟩)
  · exact hn r hr
  · exact fun l => add_nonneg (mul_nonneg hpos.le (hn r hr l))
      (mul_nonneg (neg_nonneg.mpr hneg.le) (hn s hs l))

theorem join_iff (rows : Finset (Halfspace V)) (v x : Values V) :
    x ∈ above (joinRows rows v) ↔
      ∃ t ∈ Icc (0 : ℝ) 1, ∀ r ∈ rows, t * residual r v ≤ residual r x := by
  classical
  constructor
  · intro hx
    have basic : ∀ r ∈ rows, min r.2 (dot r.1 v) ≤ dot r.1 x := fun r hr =>
      hx _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr))
    have both : ∀ r ∈ rows, ∀ s ∈ rows, residual r v < 0 → 0 < residual s v →
        0 ≤ residual s v * residual r x - residual r v * residual s x := by
      intro r hr s hs hl hu
      let q := mix (residual s v) (-residual r v) r s
      have hq : q ∈ joinRows rows v := Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(r,s),Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hr,hl⟩,Finset.mem_filter.mpr ⟨hs,hu⟩⟩,rfl⟩)
      have hh : 0 ≤ residual q x := sub_nonneg.mpr (hx q hq)
      rw [show q = mix _ _ _ _ from rfl,residual_mix] at hh
      linarith
    let ub := fun s : Option ↥rows => s.elim 1 (fun r =>
      if 0 < residual r.val v then residual r.val x / residual r.val v else 1)
    have nonneg : ∀ r ∈ rows, 0 ≤ residual r v → 0 ≤ residual r x := by
      intro r hr h
      exact sub_nonneg.mpr (by simpa [min_eq_left (sub_nonneg.mp h)] using basic r hr)
    refine ⟨least ub,⟨le_least ?_,least_le ub none⟩,fun r hr => ?_⟩
    · rintro (_ | s)
      · exact zero_le_one
      · unfold ub; simp only [Option.elim_some]; split
        · rename_i h; exact div_nonneg (nonneg s.val s.property h.le) h.le
        · exact zero_le_one
    · rcases lt_trichotomy (residual r v) 0 with hl | he | hu
      · have hv : residual r v ≤ residual r x := sub_le_sub_right
          (by simpa [min_eq_right (sub_nonpos.mp hl.le)] using basic r hr) _
        obtain ⟨s,hs⟩ := least_attained ub
        rw [hs]
        cases s with
        | none => simpa [ub] using hv
        | some s =>
          simp only [ub,Option.elim_some]
          split
          · rename_i hu
            rw [div_mul_eq_mul_div,div_le_iff₀ hu]
            linarith [both r hr s.val s.property hl hu]
          · simpa
      · rw [he,mul_zero]; exact nonneg r hr he.ge
      · apply (le_div_iff₀ hu).mp
        simpa [ub,hu] using least_le ub (some ⟨r,hr⟩)
  · rintro ⟨t,⟨ht,ht'⟩,hx⟩ r hr
    simp only [joinRows,Finset.mem_union,Finset.mem_image,Finset.mem_product,Finset.mem_filter] at hr
    rcases hr with ⟨s,hs,rfl⟩ | ⟨⟨q,s⟩,⟨⟨hq,hl⟩,⟨hs,hu⟩⟩,rfl⟩
    · have hh := hx s hs
      unfold residual at hh
      change min _ _ ≤ dot s.1 x
      rcases le_total s.2 (dot s.1 v) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    · apply sub_nonneg.mp
      change 0 ≤ residual (mix _ _ q s) x
      rw [residual_mix]
      dsimp only at hl hu ⊢
      linarith [mul_le_mul_of_nonneg_left (hx q hq) hu.le,
        mul_le_mul_of_nonneg_left (hx s hs) (neg_nonneg.mpr hl.le)]

end OAI.Geometry.Hirsch.Layer
