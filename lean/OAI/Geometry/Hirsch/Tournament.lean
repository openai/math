import OAI.Geometry.Hirsch.Dilation

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

structure Arena (X : Type) (k : ℕ) where
  beats : X → X → Prop
  asym : ∀ a b, beats a b → ¬ beats b a
  dominate : ∀ s : Set X, s.ncard ≤ k → ∃ a ∉ s, ∀ b ∈ s, beats a b

abbrev Name (k : ℕ) := Fin ((k+1)*k+1)
abbrev Player (k : ℕ) := Name k × {s : Set (Name k) // s.ncard ≤ k}

instance (k : ℕ) : Fintype (Player k) := Fintype.ofFinite _
instance (k : ℕ) : Nonempty (Player k) := ⟨(⟨0,by omega⟩,⟨∅,by simp⟩)⟩

def arena (k : ℕ) : Arena (Player k) k where
  beats a b := b.1 ∈ a.2.val ∧ a.1 ∉ b.2.val
  asym _ _ h h' := h.2 h'.1
  dominate s hs := by
    let targets := Prod.fst '' s
    let taken := ⋃ a ∈ s, insert a.1 a.2.val
    have ht : taken.ncard ≤ (k+1)*k :=
      (Forest.union_bound s _ (k+1) (fun a _ =>
        (ncard_insert_le ..).trans (Nat.add_le_add_right a.2.property 1))).trans
          (Nat.mul_le_mul_left _ hs)
    have hf : ∃ i, i ∉ taken := by
      by_contra! hn
      have he : taken = univ := eq_univ_of_forall hn
      simp [he,Name] at ht
    obtain ⟨i,hi⟩ := hf
    let a : Player k := (i,⟨targets,(ncard_image_le (s := s) (f := Prod.fst)).trans hs⟩)
    refine ⟨a, fun ha => hi (mem_iUnion₂.mpr ⟨a,ha,mem_insert ..⟩),fun b hb => ?_⟩
    exact ⟨⟨b,hb,rfl⟩,fun hh => hi (mem_iUnion₂.mpr ⟨b,hb,mem_insert_of_mem _ hh⟩)⟩

namespace Arena

variable {X : Type} {k : ℕ} (game : Arena X k)

def before (a b : X) := a ≠ b ∧ ¬ game.beats b a

theorem order_or {a b : X} (hab : a ≠ b) : game.before a b ∨ game.before b a := by
  by_cases he : game.beats b a
  · exact .inr ⟨hab.symm,game.asym _ _ he⟩
  · exact .inl ⟨hab,he⟩

theorem chain [Finite X] (r : ℕ) (s : Set X) (hs : 2^r ≤ s.ncard) :
    ∃ l : List X, l.length = r+1 ∧ l.Pairwise game.before ∧ ∀ x ∈ l, x ∈ s := by
  have hn : s.Nonempty := nonempty_of_ncard_ne_zero (ne_of_gt ((by positivity : 0 < 2^r).trans_le hs))
  induction r generalizing s with
  | zero =>
    obtain ⟨a,ha⟩ := hn
    exact ⟨[a],rfl,by simp,by simpa⟩
  | succ r ih =>
    obtain ⟨a,ha⟩ := hn
    let left := {b ∈ s | game.before b a}
    let right := {b ∈ s | game.before a b}
    have sub : s ⊆ insert a (left ∪ right) := by
      intro b hb
      by_cases he : b = a
      · exact Or.inl he
      · exact Or.inr ((game.order_or he).imp (And.intro hb) (And.intro hb))
    have bound := (ncard_le_ncard sub).trans ((ncard_insert_le ..).trans
      (Nat.add_le_add_right (ncard_union_le left right) 1))
    rw [pow_succ] at hs
    have next : ∀ t : Set X, 2^r ≤ t.ncard →
        ∃ l : List X, l.length = r+1 ∧ l.Pairwise game.before ∧ ∀ x ∈ l, x ∈ t := by
      exact fun t ht => ih t ht (nonempty_of_ncard_ne_zero (ne_of_gt ((by positivity : 0 < 2^r).trans_le ht)))
    by_cases hh : 2^r ≤ left.ncard
    · obtain ⟨l,hl,hp,hm⟩ := next left hh
      refine ⟨l ++ [a],by simp [hl],List.pairwise_append.mpr ⟨hp,by simp,?_⟩,?_⟩
      · simpa using (show ∀ x ∈ l, game.before x a from fun x hx => (hm x hx).2)
      · intro x hx
        simp only [List.mem_append,List.mem_singleton] at hx
        exact hx.elim (fun hx => (hm x hx).1) (fun he => he.symm ▸ ha)
    · obtain ⟨l,hl,hp,hm⟩ := next right (by omega)
      refine ⟨a :: l,by simp [hl],List.pairwise_cons.mpr ⟨fun x hx => (hm x hx).2,hp⟩,?_⟩
      intro x hx
      exact (List.mem_cons.mp hx).elim (fun he => he.symm ▸ ha) (fun hx => (hm x hx).1)

end Arena

def score {X : Type} (q : ℝ) (u : X → ℝ) : List X → ℝ
  | [] => 0
  | x :: l => u x + q * score q u l

variable {X : Type} {q K delta : ℝ} {u : X → ℝ}

theorem score_pos (hq : 0 < q) {l : List X} (hn : l ≠ []) (hu : ∀ x ∈ l, 0 < u x) :
    0 < score q u l := by
  induction l with
  | nil => contradiction
  | cons x l ih =>
    have hx := hu x (by simp)
    by_cases he : l = []
    · simpa [score,he]
    · exact add_pos hx (mul_pos hq (ih he (fun y hy => hu y (List.mem_cons_of_mem _ hy))))

theorem score_le (hq : 0 ≤ q) (hh : q ≤ 1/2) (hk : 0 ≤ K) (hu : ∀ x, u x ≤ K) (l : List X) :
    score q u l ≤ 2*K := by
  induction l with
  | nil => simp [score,hk]
  | cons x l ih =>
    rw [score]
    linarith [hu x,mul_le_mul_of_nonneg_left ih hq,mul_le_mul_of_nonneg_right hh hk]

theorem Arena.select [Finite X] {r : ℕ} (game : Arena X (2^r))
    (hq : 0 < q) (hh : q ≤ 1/2) (hk : 0 ≤ K) (hsmall : q*(2*K) ≤ delta/2)
    (hu : ∀ x, u x ≤ K)
    (feas : ∀ l : List X, l.length = r+1 → l.Pairwise game.before → score q u l ≤ 0) :
    ∃ a, u a ≤ 0 ∧ (u a < -delta/2 → ∀ l : List X, l.Pairwise game.before → a ∈ l → score q u l < 0) := by
  let pos := {x | 0 < u x}
  have hb : pos.ncard < 2^r := by
    by_contra! hn
    obtain ⟨l,hl,hp,hm⟩ := game.chain r pos hn
    exact (feas l hl hp).not_gt (score_pos hq (by rintro rfl; simp at hl) hm)
  obtain ⟨a,ha,hd⟩ := game.dominate pos hb.le
  refine ⟨a,le_of_not_gt ha,fun hneg l hp hm => ?_⟩
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rw [score]
    rcases List.mem_cons.mp hm with rfl | hm
    · linarith [mul_le_mul_of_nonneg_left (score_le hq.le hh hk hu l) hq.le]
    · obtain ⟨hx,hp⟩ := List.pairwise_cons.mp hp
      have hle : u x ≤ 0 := le_of_not_gt (fun hh => (hx a hm).2 (hd x hh))
      exact add_neg_of_nonpos_of_neg hle (mul_neg_of_pos_of_neg hq (ih hp hm))

end OAI.Geometry.Hirsch.Layer
