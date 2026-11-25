import OAI.Geometry.Hirsch.Board

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Round

variable {I : Type} {n : ℕ} {w : Board I n}
  {r q : w.Round} {area : Set ℕ} {i j k g : I} {a b c : Budget} {path pre rest : List I}

theorem Trip.split (h : r.Trip area i j b path) (he : path = pre ++ g :: rest) :
    ∃ u d a, r.Trip area i u a pre ∧ w.place u ∈ area ∧ r.mark u d ∧
      w.step u d = g ∧ a + atLayer (w.layer u) ≤ b := by
  induction h generalizing pre with
  | nil => simp at he
  | @go i j k d b a path hi hm ha ht ih =>
    have more : ∀ l, path = l ++ g :: rest → pre = r.charge i d ++ l →
        ∃ u e f, r.Trip area i u f pre ∧ w.place u ∈ area ∧ r.mark u e ∧
          w.step u e = g ∧ f + atLayer (w.layer u) ≤ b := by
      intro l he' he''
      obtain ⟨u,e,f,hf,hu,hg,hkey,hb⟩ := ih he'
      rw [he'']
      exact ⟨u,e,_,.go hi hm le_rfl hf,hu,hg,hkey,by
        rw [add_assoc]; exact (add_le_add_right hb _).trans ha⟩
    by_cases hc : r.mark i d
    swap
    · exact more pre (by simpa [charge,hc] using he) (by simp [charge,hc])
    cases pre with
    | nil =>
      have hg : w.step i d = g := (List.cons.inj (by simpa only [charge,ite_eq_left hc,
        List.singleton_append,List.nil_append] using he)).1
      exact ⟨i,d,0,.nil,hi,hc,hg,by simpa using (le_self_add.trans ha)⟩
    | cons x l =>
      simp only [charge,ite_eq_left hc,List.cons_append,List.nil_append,List.cons.injEq] at he
      exact more l he.2 (by simp [charge,hc,he.1])

theorem Trip.step (hi : w.place i ∈ area) {d : Bool} (hm : r.Move i d j) :
    r.Trip area i j (atLayer (w.layer i)) (r.charge i d) := by
  simpa using Trip.go hi hm (le_refl (atLayer (w.layer i) + 0)) (.nil (b := 0))

theorem Trip.redirect (h : r.Trip area i j b (pre ++ g :: rest)) :
    r.Trip area i g b (pre ++ [g]) := by
  obtain ⟨u,d,a,hp,hu,hc,rfl,hb⟩ := h.split rfl
  simpa [charge,hc] using (hp.append (.step hu (r.basic (r.middle _ _ hc).2 d))).more hb

theorem Trip.carry {d : Bool} {s : Finset I} (h : r.Trip area i j a path)
    (hn : ¬Trial.Hit s path) (hc : (r.test area d c i).Covers s) (hb : a+b ≤ c) :
    (r.test area d b j).Covers s := by
  rintro l ⟨v,hv,ht⟩
  obtain ⟨g,hg,hs⟩ := hc _ ⟨v,hv,(h.append ht).more hb⟩
  exact ⟨g,(List.mem_append.mp hg).resolve_left (fun hh => hn ⟨g,hh,hs⟩),hs⟩

theorem transfers (d : Bool) (hb : a+b ≤ c) :
    (r.paths area a i).Transfers (r.test area d c i) (r.test area d b) := by
  rintro pre g rest ⟨j,hp⟩ s hc hn hg
  apply hp.redirect.carry _ hc hb
  rintro ⟨v,hv,hs⟩
  rcases List.mem_append.mp hv with hh | hh
  · exact hn ⟨v,hh,hs⟩
  · exact hg (List.mem_singleton.mp hh ▸ hs)

theorem Trip.bound (h : r.Trip area i j b path) (x : ℕ) :
    (Trial.keysAt w.place path {x}).card ≤ b (3*x+1) := by
  induction h with
  | nil => simp [Trial.keysAt]
  | @go i j k d b a path hi hm ha ht ih =>
    have hh := ha (3*x+1)
    simp only [Pi.add_apply] at hh
    by_cases hc : r.mark i d
    swap
    · simpa [charge,hc] using ih.trans (Nat.le_add_left .. |>.trans hh)
    have mid := (r.middle _ _ hc).1
    have eq := (w.middle_step mid hm.1 d).2
    by_cases hx : w.place i = x
    · have he : 3*x+1 = w.layer i := by unfold Middle at mid; unfold place at hx; omega
      simp only [atLayer,ite_eq_left he] at hh
      have sub : Trial.keysAt w.place (r.charge i d ++ path) {x} ⊆
          insert (w.step i d) (Trial.keysAt w.place path {x}) := by
        intro v hv; simp [charge,hc] at hv ⊢; tauto
      have := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
      omega
    · have he : Trial.keysAt w.place (r.charge i d ++ path) {x} =
          Trial.keysAt w.place path {x} := by
        ext v; simp [charge,hc]; grind
      rw [he]; omega

def tests (r : w.Round) (area : Set ℕ) (dir : Bool) (i : I) (a b : Budget) (e d : ℕ)
    (he : a ≤ flat e) (hb : a + flat d ≤ b) : Trial.Tests w.place e d where
  short := r.test area dir a i
  long := r.test area dir b i
  next := r.test area dir (flat d)
  refines := test_mono _ _ _ _ (le_self_add.trans hb)
  transfer := fun pre g rest ⟨j,_,ht⟩ => transfers dir hb pre g rest ⟨j,ht⟩
  shortBound := fun _ ⟨_,_,ht⟩ x => (ht.bound x).trans (he _)
  nextBound := fun _ _ ⟨_,_,ht⟩ x => ht.bound x

structure Finer (q r : w.Round) : Prop where
  marks : ∀ i d, q.mark i d → r.mark i d
  jumps : ∀ i d j, r.jump i d j → q.jump i d j

theorem Finer.refl (r : w.Round) : r.Finer r := ⟨fun _ _ h => h,fun _ _ _ h => h⟩

theorem Finer.trans {u : w.Round} (h : u.Finer q) (h' : q.Finer r) : u.Finer r :=
  ⟨fun i d hi => h'.marks i d (h.marks i d hi),fun i d j hj => h.jumps i d j (h'.jumps i d j hj)⟩

theorem Finer.trip (h : q.Finer r) (ht : r.Trip area i j b path) :
    ∃ l, q.Trip area i j b l ∧ l ⊆ path := by
  induction ht with
  | nil => exact ⟨[],.nil,fun _ hh => hh⟩
  | go hi hm ha ht ih =>
    obtain ⟨l,hl,hs⟩ := ih
    refine ⟨_,.go hi ⟨hm.1,hm.2.imp_right (h.jumps _ _ _)⟩ ha hl,?_⟩
    intro v hv
    rcases List.mem_append.mp hv with hh | hh
    · obtain ⟨hc,he⟩ := q.charge_mem.mp hh
      exact List.mem_append_left _ (r.charge_mem.mpr ⟨h.marks _ _ hc,he⟩)
    · exact List.mem_append_right _ (hs hh)

theorem Finer.test (h : q.Finer r) {d : Bool} (hb : a ≤ b) :
    (r.test area d a i).Refines (q.test area d b i) := by
  rintro s hc path ⟨j,hj,ht⟩
  obtain ⟨l,hl,hs⟩ := h.trip ht
  obtain ⟨g,hg,hm⟩ := hc _ ⟨j,hj,hl.more hb⟩
  exact ⟨g,hs hg,hm⟩

end OAI.Geometry.Hirsch.Layer.Board.Round
