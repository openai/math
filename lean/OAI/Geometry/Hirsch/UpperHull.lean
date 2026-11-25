import OAI.Geometry.Hirsch.ProjectionRows

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {V : ℕ}

def upperHull (s : Finset (Values V)) : Set (Values V) :=
  {x | ∃ y ∈ convexHull ℝ (s : Set (Values V)), y ≤ x}

theorem upper_mem {s : Finset (Values V)} {v : Values V} (hv : v ∈ s) : v ∈ upperHull s :=
  ⟨v,subset_convexHull _ _ hv,le_rfl⟩

theorem upper_bound {s : Finset (Values V)} {x c : Values V} {a : ℝ}
    (hc : 0 ≤ c) (hs : ∀ y ∈ s, a ≤ dot c y) (hx : x ∈ upperHull s) : a ≤ dot c x := by
  obtain ⟨y,hy,hh⟩ := hx
  exact le_trans (convexHull_min hs ((convex_Ici a).linear_preimage (dot c)) hy) (dot_mono hc hh)

theorem upper_vertex {s : Finset (Values V)} {x : Values V} (hx : x ∈ (upperHull s).extremePoints ℝ) :
    x ∈ s := by
  obtain ⟨y,hy,hle⟩ := hx.1
  have he : y = x := by
    have hp : x ∈ openSegment ℝ y (x+x-y) := ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by module⟩
    apply (mem_extremePoints.mp hx).2 y ⟨y,hy,le_rfl⟩ (x+x-y) _ hp |>.1
    exact ⟨y,hy,fun l => by change y l ≤ x l + x l - y l; linarith [hle l]⟩
  subst y
  apply extremePoints_convexHull_subset (𝕜 := ℝ)
  exact mem_extremePoints.mpr ⟨hy,fun u hu v hv hh =>
    (mem_extremePoints.mp hx).2 u ⟨u,hu,le_rfl⟩ v ⟨v,hv,le_rfl⟩ hh⟩

def axes (V : ℕ) : Finset (Halfspace V) := Finset.univ.image (fun l => (Pi.single l 1,0))

theorem axis_mem (l : Fin V) : (Pi.single l 1,0) ∈ axes V := Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem axis_nonneg (l : Fin V) : (0 : Values V) ≤ Pi.single l 1 := by
  intro j; simp [Pi.single_apply]; split <;> norm_num

structure Models (rows : Finset (Halfspace V)) (s : Finset (Values V)) : Prop where
  proj : axes V ⊆ rows
  nonneg : ∀ r ∈ rows, 0 ≤ r.1
  body : above rows = upperHull s

theorem Models.join {rows : Finset (Halfspace V)} {s : Finset (Values V)} (model : Models rows s)
    {v : Values V} (hv : 0 ≤ v) : Models (joinRows rows v) (insert v s) := by
  classical
  have hn := join_nonneg v model.nonneg
  refine ⟨?_,hn,Subset.antisymm ?_ ?_⟩
  · intro r hr
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_union_left
    refine Finset.mem_image.mpr ⟨_,model.proj (axis_mem l),?_⟩
    simp [min_eq_left (show 0 ≤ v l from hv l)]
  · intro x hx
    obtain ⟨t,⟨ht,ht'⟩,hh⟩ := (join_iff ..).mp hx
    have ins : v ∈ convexHull ℝ (↑(insert v s) : Set (Values V)) := subset_convexHull _ _ (by simp)
    rcases ht'.eq_or_lt with rfl | ht'
    · refine ⟨v,ins,fun l => ?_⟩
      simpa [residual] using hh _ (model.proj (axis_mem l))
    · let y := (1-t)⁻¹ • (x - t • v)
      have hy : y ∈ above rows := by
        intro r hr
        have hb := hh r hr
        unfold residual at hb
        simp only [y,map_smul,map_sub,smul_eq_mul]
        rw [inv_mul_eq_div,le_div_iff₀ (sub_pos.mpr ht')]
        linarith
      obtain ⟨z,hz,hzy⟩ := model.body ▸ hy
      have hz' : z ∈ convexHull ℝ (↑(insert v s) : Set (Values V)) :=
        convexHull_mono (by simp) hz
      refine ⟨t • v + (1-t) • z,convex_convexHull ℝ _ ins hz' ht (by linarith) (by ring),fun l => ?_⟩
      have hb : z l ≤ (1-t)⁻¹ * (x l - t * v l) := hzy l
      rw [inv_mul_eq_div,le_div_iff₀ (sub_pos.mpr ht')] at hb
      change t * v l + (1-t)*z l ≤ x l
      linarith
  · intro x hx r hr
    apply upper_bound (hn _ hr) _ hx
    intro y hy
    suffices y ∈ above (joinRows rows v) from this _ hr
    apply (join_iff ..).mpr
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨1,by simp,by simp⟩
    · have he := model.body.symm ▸ upper_mem hy
      exact ⟨0,by simp,fun q hq => by rw [zero_mul]; exact sub_nonneg.mpr (he q hq)⟩

def costRows (V : ℕ) : ℕ → ℕ
  | 0 => V+1
  | k+1 => costRows V k + (costRows V k)^2

theorem costRows_mono (V : ℕ) : Monotone (costRows V) :=
  monotone_nat_of_le_succ (fun _ => Nat.le_add_right ..)

theorem upper_model (s : Finset (Values V)) (hs : ∀ v ∈ s, 0 ≤ v) :
    ∃ rows, Models rows s ∧ rows.card ≤ costRows V s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨insert (0,1) (axes V),⟨Finset.subset_insert ..,?_,?_⟩,?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact le_rfl
      · obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hr
        exact axis_nonneg l
    · ext x
      simp [above,upperHull]
    · exact (Finset.card_insert_le ..).trans (Nat.add_le_add_right
        (Finset.card_image_le.trans_eq (Fintype.card_fin _)) 1)
  | @insert v s hv ih =>
    obtain ⟨rows,hm,hc⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
    refine ⟨_,hm.join (hs v (by simp)),?_⟩
    rw [Finset.card_insert_of_notMem hv,costRows]
    exact (join_size ..).trans (Nat.add_le_add hc (Nat.pow_le_pow_left hc _))

end OAI.Geometry.Hirsch.Layer
