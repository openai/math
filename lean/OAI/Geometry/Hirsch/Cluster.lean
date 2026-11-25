import OAI.Geometry.Hirsch.Direction

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Coins

variable {Bit I : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] (coin : Coins Bit)

theorem selected {S : Set Bit} {pick : Table Bit → Option I} (hp : Table.Reads S pick)
    (ev : I → Table Bit → Prop) {U : ℝ} (hu : 0 ≤ U)
    (hh : ∀ i, Table.Reads Sᶜ (ev i) ∧ coin.law.prob (ev i) ≤ U) :
    coin.law.prob (fun x => ∃ i, pick x = some i ∧ ev i x) ≤ U := by
  let chosen := fun i x => pick x = some i
  have mass : ∑ i, coin.law.prob (chosen i) ≤ 1 := by
    have hm := coin.law.multiplicity Finset.univ chosen (fun _ => True) (M := 1) (by
      intro x
      apply Finset.card_le_one.mpr
      intro i hi j hj
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
      exact Option.some.inj (hi.symm.trans hj)) (by simp)
    simpa [coin.law.certain (fun _ => True.intro)] using hm
  calc
    _ ≤ ∑ i, coin.law.prob (fun x => chosen i x ∧ ev i x) := coin.law.union _
    _ ≤ ∑ i, coin.law.prob (chosen i)*U := by
      apply Finset.sum_le_sum
      intro i _
      have h : Table.Reads Sᶜᶜ (chosen i) := by
        rw [compl_compl]
        exact fun x y hx => congrArg (· = some i) (hp x y hx)
      rw [coin.independent h (hh i).1]
      exact mul_le_mul_of_nonneg_left (hh i).2 (coin.law.positive _)
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left hu mass

end Coins

namespace Board.Round

variable {I : Type} {n : ℕ} {w : Board I n} {r : w.Round} {d : Bool} {area A B : Set ℕ}
  {i j : I} {b : Budget} {l : List I}

def portion (area : Set ℕ) (b : Budget) : Budget := fun x => if x/3 ∈ area then b x else 0

theorem Trip.portion (ht : r.Trip area i j b l) : r.Trip area i j (portion area b) l := by
  induction ht with
  | nil => exact .nil
  | @go i j k d b a path hi hm ha ht ih =>
    refine .go hi hm ?_ ih
    intro x
    by_cases hx : x/3 ∈ area
    · simpa [Round.portion,hx] using ha x
    · have hh : x ≠ w.layer i := fun e => hx (e.symm ▸ hi)
      simp [Round.portion,hx,atLayer,hh]

theorem Trip.join {k : I} {path : List I} (ht : r.Trip A i j b l) (hu : r.Trip B j k b path)
    (hd : Disjoint A B) : r.Trip (A ∪ B) i k b (l ++ path) := by
  apply ((ht.portion.widen Set.subset_union_left).append (hu.portion.widen Set.subset_union_right)).more
  intro x
  by_cases hx : x/3 ∈ A
  · have := Set.disjoint_left.mp hd hx; simp [Round.portion,hx,this]
  · simp only [Pi.add_apply,Round.portion,ite_eq_right hx,zero_add]; split <;> omega

theorem Trip.exits (ht : r.Trip area i j b l) (hi : w.place i ∈ area)
    (hj : w.place j ∉ area) (hs : w.Shore (!d) j) :
    ∃ x ∈ area, if d then x+1 = w.place j else w.place j+1 = x := by
  induction ht with
  | nil => contradiction
  | @go i j k e b a path h hm ha ht ih =>
    by_cases hh : w.place j ∈ area
    · exact ih hh hj hs
    have he : j = k := by cases ht <;> simp_all
    subst k
    rcases hm with ⟨hl,rfl | jump⟩
    · have h₁ := w.east i hl
      have h₂ := w.west i hl
      have ne : w.place (w.step i e) ≠ w.place i := fun he => hj (he.symm ▸ hi)
      refine ⟨w.place i,hi,?_⟩
      cases d <;> cases e <;> simp [place,Shore] at hs ne ⊢ <;> omega
    · exact (hh ((show w.place j = w.place i from congrArg (· / 3) (r.localJump _ _ _ jump).2.1).symm ▸ hi)).elim

def Precedes (d : Bool) (A B : Set ℕ) := ∀ x ∈ A, ∀ y ∈ B, if d then x < y else y < x

theorem Precedes.disjoint (h : Precedes d A B) : Disjoint A B :=
  Set.disjoint_left.mpr fun x hx hy => by have := h x hx x hy; split at this <;> omega

theorem Precedes.ends (h : Precedes d A B) (hi : w.place i ∈ B)
    (ht : r.Trip B i j b l) (he : Ends w B d j) : Ends w (A ∪ B) d j := by
  rcases he with ⟨hj,hn⟩ | ⟨hj,hs⟩
  · exact .inl ⟨.inr hj,hn⟩
  obtain ⟨x,hx,he⟩ := ht.exits hi hj hs
  have hn : w.place j ∉ A := by
    intro hh
    have := h _ hh x hx
    cases d <;> simp_all <;> omega
  exact .inr ⟨fun hh => hh.elim hn hj,hs⟩

def restrict (w : Board I n) (area : Set ℕ) (s : Finset I) := s.filter fun g => w.place g ∈ area

theorem Trip.hit (ht : r.Trip area i j b l) (s : Finset I) :
    Trial.Hit (restrict w area s) l ↔ Trial.Hit s l :=
  ⟨fun h => h.mono (Finset.filter_subset ..),fun ⟨g,hg,hm⟩ => ⟨g,hg,Finset.mem_filter.mpr ⟨hm,(ht.member hg).1⟩⟩⟩

variable {Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {a : Table Bit → Finset I} {R : ℕ}

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem reads_cover {S : Set Bit}
    (read : ∀ g, w.place g ∈ area → w.rank g < w.rank i → Table.Reads S (fun x => g ∈ a x)) :
    Table.Reads S (r.Cover area d R a i) := by
  intro x y h
  have eq : ∀ l ∈ r.test area d (flat R) i, Trial.Hit (a x) l ↔ Trial.Hit (a y) l := by
    rintro l ⟨j,_,ht⟩
    have same := fun g hg => read g (ht.member hg).1 (ht.member hg).2 x y h
    exact ⟨fun ⟨g,hg,hm⟩ => ⟨g,hg,(same g hg).mp hm⟩,fun ⟨g,hg,hm⟩ => ⟨g,hg,(same g hg).mpr hm⟩⟩
  exact propext ⟨fun hc l hl => (eq l hl).mp (hc l hl),fun hc l hl => (eq l hl).mpr (hc l hl)⟩

structure Cap (coin : Coins Bit) (r : w.Round) (d : Bool) (R : ℕ) (a : Table Bit → Finset I)
    (area : Set ℕ) (S : Set Bit) (U : ℝ) : Prop where
  nonneg : 0 ≤ U
  reads : ∀ i, w.place i ∈ area → Table.Reads S (fun x => i ∈ a x)
  bound : ∀ i, w.place i ∈ area → coin.law.prob (r.Cover area d R a i) ≤ U

theorem Cap.join {S T : Set Bit} {U V : ℝ} (ha : Cap coin r d R a A S U) (hb : Cap coin r d R a B T V)
    (h : Precedes d A B) (hd : Disjoint S T) : Cap coin r d R a (A ∪ B) (S ∪ T) (U+V) := by
  refine ⟨add_nonneg ha.nonneg hb.nonneg,fun i hi => hi.elim (fun h => (ha.reads i h).mono Set.subset_union_left)
    (fun h => (hb.reads i h).mono Set.subset_union_right),?_⟩
  intro i hi
  rcases hi with hi | hi
  swap
  · apply le_trans _ ((hb.bound i hi).trans (le_add_of_nonneg_left ha.nonneg))
    apply coin.law.mono
    rintro x hc l ⟨j,he,ht⟩
    exact hc _ ⟨j,h.ends hi ht he,ht.widen Set.subset_union_right⟩
  let missed := fun s j => ∃ l, Ends w A d j ∧ r.Trip A i j (flat R) l ∧ ¬Trial.Hit s l
  let pick := fun s => if hh : ∃ j, missed s j then some hh.choose else none
  let sel := fun x => pick (restrict w A (a x))
  have reads : Table.Reads S sel := by
    intro x y he
    apply congrArg pick
    ext g
    by_cases hg : w.place g ∈ A
    · simpa [restrict,hg] using iff_of_eq (ha.reads g hg x y he)
    · simp [restrict,hg]
  let ev := fun j x => w.place j ∈ B ∧ r.Cover B d R a j x
  have hh := coin.selected reads ev hb.nonneg (by
    intro j
    constructor
    · have hr : Table.Reads T (r.Cover B d R a j) := reads_cover (fun g hg _ => hb.reads g hg)
      exact fun x y he => congrArg (And (w.place j ∈ B)) (hr x y (he.mono (fun _ ht hs => Set.disjoint_left.mp hd hs ht)))
    · by_cases hj : w.place j ∈ B
      · exact (coin.law.mono fun _ hh => hh.2).trans (hb.bound j hj)
      · simpa [ev,hj,Law.prob] using hb.nonneg)
  apply le_trans _ ((coin.law.either _ _).trans (add_le_add (ha.bound i hi) hh))
  apply coin.law.mono
  intro x hc
  by_cases hc' : r.Cover A d R a i x
  · exact .inl hc'
  right
  have ex : ∃ j, missed (restrict w A (a x)) j := by
    obtain ⟨l,⟨j,he,ht⟩,hm⟩ := Trial.missed hc'
    exact ⟨j,l,he,ht,fun h => hm ((ht.hit _).mp h)⟩
  obtain ⟨l,he,ht,hm⟩ := ex.choose_spec
  have hn : ¬Trial.Hit (a x) l := fun hh => hm ((ht.hit _).mpr hh)
  have hj : w.place ex.choose ∈ B := by
    by_contra h'
    apply hn (hc _ ⟨_,?_,ht.widen Set.subset_union_left⟩)
    exact he.imp (fun h => ⟨.inl h.1,h.2⟩) (fun h => ⟨fun hh => hh.elim h.1 h',h.2⟩)
  refine ⟨ex.choose,by simp [sel,pick,ex],hj,?_⟩
  rintro l' ⟨k,hk,hu⟩
  obtain ⟨g,hg,hga⟩ := hc _ ⟨k,h.ends hj hu hk,ht.join hu h.disjoint⟩
  exact ⟨g,(List.mem_append.mp hg).resolve_left (fun h => hn ⟨g,h,hga⟩),hga⟩

end Board.Round
end OAI.Geometry.Hirsch.Layer
