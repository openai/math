import OAI.Geometry.Hirsch.ModuleVertex

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

open Forest

variable {I : Type} {L V h B N C : ℕ} {code : Bundles L V}
  {tree : Forest I (Fin V) h} {ep : Episodes N}

def origin (i : I) (pos : Position V) (b : Fin B) :=
  insert (i,some b,pos) (keys B (i,pos.2))

theorem origin_bound (i : I) (pos : Position V) (b : Fin B) : (origin i pos b).ncard ≤ 3 :=
  (ncard_insert_le ..).trans (Nat.add_le_add_right ((ncard_insert_le ..).trans (by simp)) 1)

theorem origin_roles (i : I) (pos : Position V) (b : Fin B) {x : Port I B V} (hx : x ∈ origin i pos b) :
    x.1 = i ∧ (x.2.1 = none ∨ x.2.1 = some b) := by
  rcases hx with rfl | rfl | rfl <;> simp

theorem price_vanish {x : Space I B V} {i : I} {l : Fin V} (hz : ∀ y ∈ keys B (i,l), x y = 0) :
    W i l x = 0 ∧ P i l x = 0 := by
  have hw := hz (i,none,false,l) (by simp [keys])
  have hp := hz (i,none,true,l) (by simp [keys])
  simp [P,W,hw,hp]

theorem output_vanish (eps : I → ℝ) (i : I) (pos : Position V) (b : Fin B) {x : Space I B V}
    (hz : ∀ y ∈ origin i pos b ∪ tree.prices B i, x y = 0) (k : ℕ) :
    output tree eps i pos b k x = 0 := by
  induction k with
  | zero =>
    obtain ⟨hw,hp⟩ := price_vanish (fun y hy => hz y (.inl (.inr hy)))
    have ht := hz (i,some b,pos) (.inl (.inl rfl))
    simp only [output,quick,base,LinearMap.add_apply,terminal,LinearMap.proj_apply,ht,add_zero]
    split
    · split <;> assumption
    · rfl
  | succ k ih =>
    by_cases hk : k < tree.depth i
    · rw [output_next _ _ _ _ _ hk,ih,mul_zero,add_zero,tree.node_next i hk]
      apply And.right
      apply price_vanish
      intro y hy
      apply hz y
      exact .inr (mem_iUnion₂.mpr ⟨_,List.getElem_mem hk,hy⟩)
    · simpa [output,hk] using ih

namespace Plan

variable (plan : Plan tree code ep B C)

theorem support_of_vanish (r : plan.Rows) (s : Set (Port I B V))
    (hz : ∀ x, (∀ y ∈ s, x y = 0) → plan.coeff r x = 0) : plan.block.support r ⊆ s := by
  classical
  intro y hy
  by_contra hn
  apply hy
  apply hz
  intro j hj
  have : j ≠ y := fun he => hn (he ▸ hj)
  simp [this]

theorem red_support (i : I) (pos : Position V) (b : Fin B) :
    tree.Footprint b b i 3 (plan.block.support (plan.red i pos b)) := by
  refine ⟨origin i pos b,origin_bound ..,?_,plan.support_of_vanish _ _ (fun _ hz => output_vanish _ _ _ _ hz _)⟩
  intro x hx
  simpa [roles] using origin_roles i pos b hx

theorem support [NeZero V] (r : plan.Rows) :
    ∃ b d i, tree.Footprint b d i (6*V) (plan.block.support r) := by
  have hv := NeZero.pos V
  rcases r with ⟨i,r⟩ | ⟨i,pos,b⟩ | ⟨i,pos,k,t,b,d⟩
  · obtain ⟨b,hb⟩ := (plan.panel i).localizes r
    let f : Bool × Position V → Port I B V := fun y => (i,if y.1 then some b else none,y.2)
    refine ⟨b,b,i,range f,?_,?_,?_⟩
    · have hh := ncard_image_le (s := univ) (f := f)
      simp [Position] at hh
      omega
    · rintro _ ⟨⟨_ | _,pos⟩,rfl⟩ <;> simp [roles,f]
    · apply plan.support_of_vanish
      exact fun x hz => hb x (fun pos =>
        ⟨hz _ (.inl ⟨(false,pos),rfl⟩),hz _ (.inl ⟨(true,pos),rfl⟩)⟩)
  · obtain ⟨s,hs,hr,hh⟩ := plan.red_support i pos b
    exact ⟨b,b,i,s,by omega,hr,hh⟩
  · refine ⟨b,d,i,origin i pos b ∪ origin i pos d,?_,?_,?_⟩
    · exact (ncard_union_le ..).trans ((Nat.add_le_add (origin_bound ..) (origin_bound ..)).trans (by omega))
    · rintro x (hx | hx)
      · obtain ⟨he,hb⟩ := origin_roles _ _ _ hx
        exact ⟨he,hb.imp_right Or.inl⟩
      · obtain ⟨he,hd⟩ := origin_roles _ _ _ hx
        exact ⟨he,hd.imp_right Or.inr⟩
    · apply plan.support_of_vanish
      intro x hz
      have hb := output_vanish (tree := tree) plan.eps i pos b (fun y hy => hz y (hy.imp_left Or.inl)) k
      have hd := output_vanish (tree := tree) plan.eps i pos d (fun y hy => hz y (hy.imp_left Or.inr)) k
      simp only [coeff]
      split <;> simp [hb,hd]

end Plan
end OAI.Geometry.Hirsch.Layer
