import OAI.Geometry.Hirsch.Locality

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

abbrev Edges (X L : Type) := X → L → X

namespace Edges

variable {X L A : Type} [Fintype L] (f : Edges X L)

def ball : ℕ → X → Finset X
  | 0,i => {i}
  | k+1,i => insert i (Finset.univ.biUnion fun l => ball k (f i l))

theorem root (k : ℕ) (i : X) : i ∈ f.ball k i := by cases k <;> simp [ball]

theorem sub (k : ℕ) (i : X) (a : L) : f.ball k (f i a) ⊆ f.ball (k+1) i := by
  intro j hj; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,hj⟩)

theorem grow (i : X) {k m : ℕ} (hm : k ≤ m) : f.ball k i ⊆ f.ball m i := by
  induction k generalizing m i with
  | zero => simpa [ball] using f.root m i
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m =>
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact f.root _ _
      · obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp hj
        exact f.sub _ _ a (ih _ (by omega) ha)

def bound (L : Type) [Fintype L] (k : ℕ) := (Fintype.card L+1)^k

theorem card (k : ℕ) (i : X) : (f.ball k i).card ≤ bound L k := by
  induction k generalizing i with
  | zero => simp [ball,bound]
  | succ k ih =>
    unfold ball
    apply (Finset.card_insert_le ..).trans
    have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ih (f i a))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
    have hh := Finset.card_biUnion_le.trans h
    have pos : 0 < bound L k := by unfold bound; positivity
    rw [show bound L (k+1) = Fintype.card L*bound L k + bound L k by simp [bound,pow_succ',add_mul]]
    exact Nat.add_le_add hh pos

theorem decreasing (rank : X → ℕ) (hr : ∀ i a, rank (f i a) ≤ rank i) (k : ℕ) (i : X) :
    ∀ j ∈ f.ball k i, rank j ≤ rank i := by
  induction k generalizing i with
  | zero => simp [ball]
  | succ k ih =>
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rfl
    · obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp hj
      exact (ih _ _ ha).trans (hr _ a)

def View (L A : Type) : ℕ → Type
  | 0 => A
  | k+1 => View L A k × (L → View L A k)

instance viewFinite [Fintype A] (k : ℕ) : Fintype (View L A k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype A)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (View L A k × (L → View L A k)))

def view (a : X → A) : ∀ k, X → View L A k
  | 0,i => a i
  | k+1,i => (view a k i,fun l => view a k (f i l))

omit [Fintype L] in
theorem trunc (a : X → A) {k m : ℕ} (h : k ≤ m) {i j : X} (he : f.view a m i = f.view a m j) :
    f.view a k i = f.view a k j := by
  induction m,h using Nat.le_induction with
  | base => exact he
  | succ m _ ih => exact ih (congrArg Prod.fst he)

omit [Fintype L] in
theorem targets (a : X → A) {k : ℕ} {i j : X} (he : f.view a (k+1) i = f.view a (k+1) j) (l : L) :
    f.view a k (f i l) = f.view a k (f j l) := congrFun (congrArg Prod.snd he) l

def tally (a : X → A) (k : ℕ) (i : X) := (f.ball k i).image a

def score (a : X → A) (S : Finset A) (m : ℕ) (i : X) :=
  ∑ k ∈ Finset.range (m+1), ((f.tally a k i) ∩ S).card

theorem score_falls (a : X → A) (S : Finset A) {m : ℕ} (hs : S.card ≤ m) {i : X} {l : L}
    (hi : a i ∈ S) (hn : a i ∉ f.tally a m (f i l)) :
    f.score a S m (f i l) < f.score a S m i := by
  let c := fun i k => ((f.tally a k i) ∩ S).card
  have step : ∀ k ∈ Finset.range m, c (f i l) k + 1 ≤ c i (k+1) := by
    intro k hk
    have sub := Finset.image_mono a (f.sub k i l)
    have notin : a i ∉ f.tally a k (f i l) :=
      fun h => hn (Finset.image_mono a (f.grow _ (Finset.mem_range.mp hk).le) h)
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_inter sub Finset.Subset.rfl,fun he => ?_⟩
    have hh : a i ∈ f.tally a (k+1) i ∩ S :=
      Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ (f.root _ _),hi⟩
    exact notin (Finset.mem_inter.mp (he.symm ▸ hh)).1
  have hh := Finset.sum_le_sum step
  have pos : 0 < c i 0 := Finset.card_pos.mpr
    ⟨a i,Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ (f.root _ _),hi⟩⟩
  have last : c (f i l) m ≤ m := (Finset.card_le_card Finset.inter_subset_right).trans hs
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,mul_one] at hh
  change (∑ k ∈ Finset.range (m+1), c (f i l) k) < ∑ k ∈ Finset.range (m+1), c i k
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  omega

end Edges
end OAI.Geometry.Hirsch.Layer
