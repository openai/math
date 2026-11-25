import OAI.Geometry.Hirsch.Redirect

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I : Type} {n : ℕ} (w : Board I n)

theorem shore_inj {d e : Bool} {i : I} (h : w.Shore d i) (h' : w.Shore e i) : d = e := by
  cases d <;> cases e <;> simp_all [Shore]

theorem shore_cross {i : I} {d : Bool} (hi : w.live i) (h : w.place (w.step i d) ≠ w.place i) :
    w.Shore (!d) (w.step i d) := by
  have := w.east i hi
  have := w.west i hi
  cases d <;> simp [place,Shore] at * <;> omega

inductive Ray (area : Set ℕ) (d : Bool) : I → I → Prop
  | self {i} : Ray area d i i
  | go {i j} (hi : w.place i ∈ area) (hl : w.live i) (rest : Ray area d (w.step i d) j) :
      Ray area d i j

variable {w} {area : Set ℕ} {d : Bool} {i j k g : I}

theorem Ray.join (h : w.Ray area d i j) (h' : w.Ray area d j k) : w.Ray area d i k := by
  induction h with
  | self => exact h'
  | go hi hl ht ih => exact .go hi hl (ih h')

theorem Ray.forward (h : w.Ray area d i j) : w.loc d i ≤ w.loc d j := by
  induction h with
  | self => rfl
  | go hi hl ht ih => rw [w.loc_step d hl] at ih; omega

theorem Ray.ordered (h : w.Ray area d i j) (h' : w.Ray area d i k)
    (hle : w.loc d j ≤ w.loc d k) : w.Ray area d j k := by
  induction h with
  | self => exact h'
  | go hi hl ht ih =>
    cases h' with
    | self => have := ht.forward; rw [w.loc_step d hl] at this; omega
    | go _ _ ht' => exact ih ht' hle

theorem Ray.eq_of_loc (h : w.Ray area d i j) (he : w.loc d i = w.loc d j) : i = j := by
  cases h with
  | self => rfl
  | go hi hl ht => have := ht.forward; rw [w.loc_step d hl] at this; omega

theorem Ray.reach (w : Board I n) (area : Set ℕ) (d : Bool) : ∀ i, w.place i ∈ area →
    ∃ j, w.Ray area d i j ∧ Round.Ends w area d j := by
  apply w.induct
  intro i ih hi
  by_cases hl : w.live i
  swap
  · exact ⟨i,.self,.inl ⟨hi,hl⟩⟩
  by_cases hj : w.place (w.step i d) ∈ area
  · obtain ⟨j,ht,he⟩ := ih hl d hj
    exact ⟨j,.go hi hl ht,he⟩
  · exact ⟨_,.go hi hl .self,.inr ⟨hj,w.shore_cross hl (fun he => hj (he.symm ▸ hi))⟩⟩

namespace Round

variable (r : w.Round)

def On (area : Set ℕ) (d : Bool) (i g : I) :=
  ∃ u, w.Ray area d i u ∧ w.place u ∈ area ∧ r.mark u d ∧ w.step u d = g

variable {r}

theorem On.info (h : r.On area d i g) : w.Shore d g ∧ w.place g ∈ area ∧
    w.Ray area d i g ∧ w.loc d i < w.loc d g := by
  obtain ⟨u,hr,hu,hm,rfl⟩ := h
  obtain ⟨hm,hl⟩ := r.middle _ _ hm
  obtain ⟨hg,he⟩ := w.middle_step hm hl d
  exact ⟨hg,he.symm ▸ hu,hr.join (.go hu hl .self),by rw [w.loc_step d hl]; exact Nat.lt_succ_of_le hr.forward⟩

theorem On.strict (h : r.On area d i g) (hi : w.Shore d i) : w.num d i < w.num d g := by
  have := h.info.2.2.2
  have := (w.shore_loc d i).mp hi
  unfold num; omega

theorem On.extend (h : r.On area d j g) (hr : w.Ray area d i j) : r.On area d i g := by
  obtain ⟨u,h,hu,hm,he⟩ := h
  exact ⟨u,hr.join h,hu,hm,he⟩

theorem On.later (h : r.On area d i g) (hr : w.Ray area d i j) (hj : w.num d j < w.num d g) :
    r.On area d j g := by
  obtain ⟨u,h,hu,hm,rfl⟩ := h
  refine ⟨u,hr.ordered h ?_,hu,hm,rfl⟩
  have := w.loc_step d (r.middle _ _ hm).2
  unfold num at hj; omega

theorem On.unique (h : r.On area d i j) (h' : r.On area d i k) (he : w.place j = w.place k) : j = k := by
  have he' := (w.same d j k).mpr he
  have := (w.shore_loc d j).mp h.info.1
  have := (w.shore_loc d k).mp h'.info.1
  have hh : w.loc d j = w.loc d k := by unfold num at he'; omega
  exact (h.info.2.2.1.ordered h'.info.2.2.1 hh.le).eq_of_loc hh

theorem Finer.on {q : w.Round} (h : q.Finer r) (hg : q.On area d i g) : r.On area d i g := by
  obtain ⟨u,hr,hu,hm,he⟩ := hg
  exact ⟨u,hr,hu,h.marks _ _ hm,he⟩

theorem trace (r : w.Round) (h : w.Ray area d i j) :
    ∃ path b, r.Trip area i j b path ∧ b + w.ahead d j = w.ahead d i ∧
      ∀ g ∈ path, r.On area d i g ∧ w.loc d g ≤ w.loc d j := by
  induction h with
  | self => exact ⟨[],0,.nil,zero_add _,by simp⟩
  | go hi hl ht ih =>
    obtain ⟨l,b,hb,he,hg⟩ := ih
    refine ⟨_,_,.go hi (r.basic hl d) le_rfl hb,by rw [add_assoc,he,w.ahead_step d hl],?_⟩
    intro g hm
    rcases List.mem_append.mp hm with hh | hh
    · obtain ⟨hc,rfl⟩ := r.charge_mem.mp hh
      exact ⟨⟨_,.self,hi,hc,rfl⟩,ht.forward⟩
    · exact ⟨(hg _ hh).1.extend (.go hi hl .self),(hg _ hh).2⟩

theorem spine (r : w.Round) (hi : w.place i ∈ area) (d : Bool) :
    ∃ l ∈ r.test area d (flat 1) i, ∀ g ∈ l, r.On area d i g := by
  obtain ⟨j,hj,he⟩ := Ray.reach w area d i hi
  obtain ⟨l,b,ht,hb,hg⟩ := r.trace hj
  exact ⟨l,⟨j,he,ht.more (le_self_add.trans (hb.le.trans (w.ahead_one d i)))⟩,fun g h => (hg g h).1⟩

theorem hits {s : Finset I} {b : Budget} (hi : w.place i ∈ area) (hb : flat 1 ≤ b)
    (hc : (r.test area d b i).Covers s) : ∃ g ∈ s, r.On area d i g := by
  obtain ⟨l,hl,hh⟩ := r.spine hi d
  obtain ⟨g,hg,hm⟩ := test_mono _ _ _ _ hb _ hc _ hl
  exact ⟨g,hm,hh _ hg⟩

theorem On.first {s t : Finset I} {b : Budget} (h : r.On area d i g) (hg : g ∈ t)
    (hb : flat 1 ≤ b) (hs : (r.paths area b i).Before s t) :
    ∃ j ∈ s, r.On area d i j ∧ w.num d j < w.num d g := by
  obtain ⟨u,hr,hu,hm,rfl⟩ := h
  obtain ⟨l,a,ht,he,hh⟩ := r.trace hr
  have hl := (r.middle _ _ hm).2
  have hf : a + atLayer (w.layer u) ≤ b := by
    rw [← w.ahead_step d hl,← add_assoc] at he
    exact le_self_add.trans (he.le.trans ((w.ahead_one d i).trans hb))
  have path := (ht.append (.step hu (r.basic hl d))).more hf
  simp only [charge,ite_eq_left hm] at path
  obtain ⟨j,hj,hjs⟩ := hs l _ [] ⟨_,path⟩ hg
  obtain ⟨ho,hj'⟩ := hh _ hj
  refine ⟨j,hjs,ho,?_⟩
  have := (w.shore_loc d j).mp ho.info.1
  have := w.loc_step d hl
  unfold num; omega

end Round
end OAI.Geometry.Hirsch.Layer.Board
