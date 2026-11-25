import OAI.Geometry.Hirsch.Occurrences

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (v : u.Valid) (z : Sample u)

def round : L.w.Round where
  mark i d := ∃ j, L.along i d j ∧ A.Occurs v z j
  middle := by
    rintro i d ⟨j,hj,_⟩
    exact ⟨(L.info _ _ _ hj).1,(L.info _ _ _ hj).2.1⟩
  jump i d j := L.along i d j ∧ j ≠ i
  localJump := by
    rintro i d j ⟨h,hn⟩
    obtain ⟨_,hl,_,he,_,hh⟩ := L.info _ _ _ h
    exact ⟨hl,he,hh.resolve_left hn⟩

variable {A v z} {Q : Network u (NodeName u)} {i : X} {d : Bool}

theorem marked (h : (A.round v z).mark i d) : A.Pass v z (L.w.step i d) := by
  obtain ⟨j,hj,ho⟩ := h
  rw [← (L.info _ _ _ hj).2.2.2.2.1]; exact ho.2.2.2 d

def Models (A : L.Decoration) (z : Sample u) (Q : Network u (NodeName u)) :=
  (A.active z.1).Agree Q (A.name z.1) (Naming.P u)

theorem marks (prom : ∀ i, A.Promised v i) (hq : A.Models z Q (Network.window u+2) i)
    (h : (A.round v z).mark i d) : (Q.done v z.2.1).round.mark (A.name z.1 i) d := by
  obtain ⟨j,hj,ho⟩ := h
  obtain ⟨hm,hl,_,_,he,_⟩ := L.info _ _ _ hj
  have hmid : Q.w.Middle (A.name z.1 i) := by unfold Middle; rw [← hq.1]; exact hm
  apply Q.marks v hmid (hq.2.1.mp hl)
  intro a ha
  have earn := ho.2.2.1 a ha
  have hp : u.phase a < Naming.P u := u.phase_lt a
  unfold Network.accepts
  split
  · rename_i eq
    subst d
    rw [he] at earn
    obtain ⟨eq,hh⟩ := hq.2.2.1 (u.side a) hl
    rw [← eq]
    exact earn _ rfl Q (hh.less hp.le (Nat.le_succ _))
  · rename_i hn
    have eq : d = !(u.side a) := by cases d <;> cases h : u.side a <;> simp_all
    obtain ⟨hl,he⟩ := prom i a z.1 j (eq ▸ hj) earn
    obtain ⟨eq,hh⟩ := hq.2.2.2 a hp
    rw [← eq]
    obtain ⟨eq',hh'⟩ := hh.2.2.1 (u.side a) hl
    exact ⟨hh.2.1.mp hl,eq' ▸ he _ rfl Q (hh'.less hp.le le_rfl)⟩

theorem lift_move {j : NodeName u} {k : ℕ} (hq : A.Models z Q (k+1) i)
    (hm : (Q.done v z.2.1).round.Move (A.name z.1 i) d j) :
    ∃ y, (A.round v z).Move i d y ∧ A.name z.1 y = j ∧ A.Models z Q k y := by
  have hl := hq.2.1.mpr hm.1
  rcases hm.2 with rfl | hj
  · exact ⟨_,(A.round v z).basic hl d,hq.2.2.1 d hl⟩
  have ne : j ≠ A.name z.1 i := fun he => ((Q.done v z.2.1).round.falls hm).ne (congrArg Q.w.rank he)
  obtain ⟨a,ha,hd,he⟩ := Q.final_fits v _ _ _ _ hj
  obtain ⟨hh,ht⟩ := hq.2.2.2 a ha
  have eq : A.name z.1 ((A i).slot a z.1) = j := hh.trans he
  have hn : (A i).slot a z.1 ≠ i := fun h => ne (eq.symm.trans (congrArg _ h))
  have along := ((A i).valid a z.1).resolve_left hn
  exact ⟨_,⟨hl,.inr ⟨hd.symm ▸ along,hn⟩⟩,eq,ht⟩

theorem lift_trip (prom : ∀ i, A.Promised v i) {b : Budget} {x y : NodeName u} {path : List (NodeName u)} {s : ℕ}
    (ht : (Q.done v z.2.1).round.Trip Set.univ x y b path) (dead : ¬Q.w.live y)
    (allow : ∀ g ∈ path, Q.passes v z.2.1 z.2.2 g → Q.w.place g = s)
    (he : A.name z.1 i = x) (hq : A.Models z Q (Network.window u+2+Network.total u b) i) :
    ∃ j l, ¬L.w.live j ∧ (A.round v z).Trip Set.univ i j b l ∧ ∀ g ∈ l, L.w.place g = s := by
  induction ht generalizing i with
  | nil =>
    have hh := Network.Agree.cut hq (show 1 ≤ _ by omega)
    exact ⟨i,[],fun hl => dead (he ▸ hh.2.1.mp hl),.nil,by simp⟩
  | @go x y endpt d b a path hi hm ha ht ih =>
    subst x
    have spend := Network.total_spend (u := u) (Q.w.bound _) ha
    have hh := Network.Agree.cut hq (show Network.window u+2+Network.total u a+1 ≤ _ by omega)
    obtain ⟨j,hj,he,hq'⟩ := lift_move hh hm
    obtain ⟨k,l,hdead,ht,hgood⟩ := ih dead (fun _ h => allow _ (List.mem_append_right _ h)) he hq'
    refine ⟨k,_,hdead,.go (Set.mem_univ _) hj (hh.1.symm ▸ ha) ht,?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    swap
    · exact hgood _ hg
    obtain ⟨hc,rfl⟩ := (A.round v z).charge_mem.mp hg
    obtain ⟨key,hkey⟩ := hh.2.2.1 d hj.1
    have hm := marks prom (hh.cut (by omega)) hc
    have hp := (marked hc).propagate (hkey.cut (by omega))
    have heq := (hkey.cut (show 1 ≤ _ by omega)).place
    exact heq.trans (allow _ (List.mem_append_left _ ((Q.done v z.2.1).round.charge_mem.mpr ⟨hm,key⟩)) hp)

theorem Pass.path (hp : A.Pass v z i) (prom : ∀ i, A.Promised v i) :
    ∃ j l, ¬L.w.live j ∧ (A.round v z).Trip Set.univ i j (flat (u.D u.h).step) l ∧
      ∀ g ∈ l, L.w.place g = L.w.place i := by
  obtain ⟨Q,hq,hh⟩ := hp
  have hn : u.a^u.h ≤ u.a^(u.h+1) := Nat.pow_le_pow_right (by have := v.base; omega) (by omega)
  obtain ⟨_,_,hd,ht,ha⟩ := Stage.final_path hn hh
  have eq := (hq.cut (show 1 ≤ R u by unfold R; omega)).place
  exact lift_trip prom ht hd (fun _ hg hp => (ha _ hg hp).trans eq.symm) rfl
    (hq.cut (Nat.add_le_add_left (Network.total_le u le_rfl) _))

theorem escape (prom : ∀ i, A.Promised v i) (z : Sample u) (hi : L.w.Shore d i) :
    ∃ s ≠ L.w.place i, ∃ j l, ¬L.w.live j ∧ (A.round v z).Trip Set.univ i j (flat (1+(u.D u.h).step)) l ∧
      ∀ g ∈ l, L.w.place g = s := by
  let r := A.round v z
  obtain ⟨l,⟨j,he,ht⟩,ho⟩ := r.spine (Set.mem_univ (L.w.place i)) d
  have hd := (he.resolve_right fun h => h.1 (Set.mem_univ _)).2
  cases l with
  | nil => exact ⟨L.w.place i+1,by omega,j,[],hd,ht.more (fun _ => Nat.le_add_right ..),by simp⟩
  | cons g tail =>
    have h := ho g (by simp)
    have hn := (h.strict hi).ne'
    obtain ⟨u',_,_,hm,he⟩ := h
    obtain ⟨k,l,hd,hh,hs⟩ := (he ▸ marked hm).path prom
    have pre : r.Trip Set.univ i g (flat 1) [g] := Round.Trip.redirect (pre := []) ht
    exact ⟨L.w.place g,fun e => hn ((L.w.same d _ _).mpr e),k,_,hd,pre.append hh,by simpa using hs⟩

end OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration
