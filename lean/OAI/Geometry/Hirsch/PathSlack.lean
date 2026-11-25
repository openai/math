import OAI.Geometry.Hirsch.Terms

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer.World

variable {X : Type} {n V : ℕ} (w : World X n) (D : ℕ) (ok : Fin V → X → Prop)

abbrev Mode (D : ℕ) := Bool × Fin (D+1)

def weight (n j : ℕ) (p : Mode D) := (1/4 : ℝ) ^ cost n j p.1 p.2

def entry (x : X) (l : Fin V) (p : Mode D) : ℝ := by
  classical
  exact if w.Escape (ok l) x p.1 p.2 then weight D n (w.layer x) p else 0

def slack (x : X) (l : Fin V) := -least (fun p => -w.entry D ok x l p)

theorem entry_le (x : X) (l : Fin V) (p : Mode D) : w.entry D ok x l p ≤ w.slack D ok x l := by
  unfold slack
  linarith [least_le (fun p => -w.entry D ok x l p) p]

theorem attained (x : X) (l : Fin V) : ∃ p, w.slack D ok x l = w.entry D ok x l p := by
  obtain ⟨p,hp⟩ := least_attained (fun p => -w.entry D ok x l p)
  exact ⟨p,by simp [slack,hp]⟩

theorem slack_nonneg (x : X) : 0 ≤ w.slack D ok x := by
  intro l
  obtain ⟨p,hp⟩ := w.attained D ok x l
  rw [hp]
  change 0 ≤ _
  unfold entry weight
  split <;> positivity

theorem slack_zero {x : X} {l : Fin V} (hn : ¬ok l x) : w.slack D ok x l = 0 := by
  obtain ⟨p,hp⟩ := w.attained D ok x l
  have hh : ¬w.Escape (ok l) x p.1 p.2 := fun he => hn he.good
  simp [hp,entry,hh]

theorem slack_pos {x : X} {l : Fin V} {d : Bool} (hw : w.Escape (ok l) x d D) :
    0 < w.slack D ok x l := by
  apply lt_of_lt_of_le _ (w.entry_le D ok x l (d,⟨D,by omega⟩))
  simp only [entry,hw,↓reduceIte,weight]
  positivity

theorem slack_merge {x : X} (hx : w.live x) (l : Fin V) :
    w.slack D ok x l ≤ (1/4 : ℝ) * max (w.slack D ok (w.step x false) l) (w.slack D ok (w.step x true) l) := by
  obtain ⟨⟨d,k⟩,he⟩ := w.attained D ok x l
  rw [he,entry]
  split
  · rename_i hw
    cases hw with
    | done _ hh => contradiction
    | @go _ _ e _ m _ _ hb ht =>
      have hm : m < D+1 := by have := k.isLt; omega
      let p : Mode D := (e,⟨m,hm⟩)
      have hs : weight D n (w.layer (w.step x e)) p ≤ w.slack D ok (w.step x e) l := by
        simpa [entry,p,ht] using w.entry_le D ok (w.step x e) l p
      have hc := cost_step hx hb
      calc
        _ ≤ (1/4 : ℝ) ^ (cost n (w.layer (w.step x e)) e m + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
        _ = (1/4 : ℝ) * weight D n (w.layer (w.step x e)) p := pow_succ' ..
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (hs.trans ?_) (by norm_num)
          cases e
          · exact le_max_left ..
          · exact le_max_right ..
  · exact mul_nonneg (by norm_num) ((w.slack_nonneg D ok _ l).trans (le_max_left ..))

def dictionary (V D n j : ℕ) : Finset (Values V) :=
  Finset.univ.image (fun f : Fin V → Option (Mode D) => fun l => (f l).elim 0 (weight D n j))

theorem slack_mem (x : X) : w.slack D ok x ∈ dictionary V D n (w.layer x) := by
  classical
  have hh : ∀ l, ∃ m : Option (Mode D), m.elim 0 (weight D n (w.layer x)) = w.slack D ok x l := by
    intro l
    obtain ⟨p,hp⟩ := w.attained D ok x l
    rw [hp,entry]
    split
    · exact ⟨some p,rfl⟩
    · exact ⟨none,rfl⟩
  choose f hf using hh
  exact Finset.mem_image.mpr ⟨f,Finset.mem_univ _,funext hf⟩

def states (j : ℕ) : Finset (Values V) := by
  classical
  exact (dictionary V D n j).filter (fun y => n ≤ j ∧ y = 0 ∨ ∃ x, w.layer x = j ∧ w.slack D ok x = y)

theorem state_mem (x : X) : w.slack D ok x ∈ w.states D ok (w.layer x) := by
  classical
  exact Finset.mem_filter.mpr ⟨w.slack_mem D ok x,.inr ⟨x,rfl,rfl⟩⟩

theorem state_cases {j : ℕ} {y : Values V} (hy : y ∈ w.states D ok j) :
    n ≤ j ∧ y = 0 ∨ ∃ x, w.layer x = j ∧ w.slack D ok x = y := by
  classical
  exact (Finset.mem_filter.mp hy).2

theorem state_count (j : ℕ) : (w.states D ok j).card ≤ (2*(D+1)+1)^V := by
  classical
  unfold states
  apply (Finset.card_filter_le ..).trans
  unfold dictionary
  apply Finset.card_image_le.trans
  simp [Mode]

theorem state_nonempty (hf : w.Full) (j : ℕ) : (w.states D ok j).Nonempty := by
  classical
  by_cases hh : j < n
  · obtain ⟨x,rfl⟩ := hf.1 j hh
    exact ⟨_,w.state_mem D ok x⟩
  · refine ⟨0,Finset.mem_filter.mpr ⟨?_,.inl ⟨by omega,rfl⟩⟩⟩
    exact Finset.mem_image.mpr ⟨fun _ => none,Finset.mem_univ _,rfl⟩

theorem sequence {L k : ℕ} {code : Bundles L V} (w : World X (L*(k+2))) (hf : w.Full)
    (hi : ∀ s (i : Fin k) x, w.layer x = micro s i → code.Identifies s (w.slack D ok x)) :
    Nonempty (StateSequence code ((2*(D+1)+1)^V) k (1/4)) := by
  refine ⟨⟨w.states D ok,w.state_count D ok,w.state_nonempty D ok hf,?_,?_,?_⟩⟩
  · intro j y hy
    rcases w.state_cases D ok hy with ⟨_,rfl⟩ | ⟨x,_,rfl⟩
    · rfl
    · exact w.slack_nonneg D ok x
  · intro s i y hy
    rcases w.state_cases D ok hy with ⟨he,_⟩ | ⟨x,hx,rfl⟩
    · exact ((micro_bound s i).not_ge he).elim
    · exact hi _ _ _ hx
  · intro j hj u hu v hv
    obtain ⟨x,hx,rfl⟩ := (w.state_cases D ok hu).resolve_left (fun h => by omega)
    obtain ⟨y,hy,rfl⟩ := (w.state_cases D ok hv).resolve_left (fun h => by omega)
    obtain ⟨z,hz,h₁,h₂⟩ := hf.2 x y (by omega)
    have he : w.layer z = j+1 := by rw [← w.west z hz,h₁,hx]
    exact ⟨_,he ▸ w.state_mem D ok z,fun l => by simpa [h₁,h₂] using w.slack_merge D ok hz l⟩

end OAI.Geometry.Hirsch.Layer.World
