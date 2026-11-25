import OAI.Geometry.Hirsch.Network

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {X Y Z : Type} (Q : Network u X) (Q' : Network u Y) (f : X → Y) (p : ℕ)

def Agree : ℕ → X → Prop
  | 0,_ => True
  | R+1,i => Q.w.layer i = Q'.w.layer (f i) ∧ (Q.w.live i ↔ Q'.w.live (f i)) ∧
      (∀ d, Q.w.live i → f (Q.w.step i d) = Q'.w.step (f i) d ∧ Agree R (Q.w.step i d)) ∧
      ∀ a, u.phase a < p → f (Q.slot a i) = Q'.slot a (f i) ∧ Agree R (Q.slot a i)

variable {Q Q' f p} {R S : ℕ} {i : X}

theorem Agree.less (h : Q.Agree Q' f p R i) {q : ℕ} (hq : q ≤ p) (hs : S ≤ R) : Q.Agree Q' f q S i := by
  induction S generalizing R i with
  | zero => exact True.intro
  | succ s ih =>
    cases R with
    | zero => omega
    | succ r =>
      exact ⟨h.1,h.2.1,fun d hl => ⟨(h.2.2.1 d hl).1,ih (h.2.2.1 d hl).2 (by omega)⟩,
        fun a ha => ⟨(h.2.2.2 a (ha.trans_le hq)).1,ih (h.2.2.2 a (ha.trans_le hq)).2 (by omega)⟩⟩

theorem Agree.cut (h : Q.Agree Q' f p R i) (hs : S ≤ R) : Q.Agree Q' f p S i := h.less le_rfl hs

theorem Agree.symm {e : X ≃ Y} (h : Q.Agree Q' e p R i) : Q'.Agree Q e.symm p R (e i) := by
  induction R generalizing i with
  | zero => exact True.intro
  | succ R ih =>
    simp only [Agree,Equiv.symm_apply_apply]
    refine ⟨h.1.symm,h.2.1.symm,?_,?_⟩
    · intro d hl
      obtain ⟨he,hh⟩ := h.2.2.1 d (h.2.1.mpr hl)
      rw [← he]; exact ⟨e.symm_apply_apply _,ih hh⟩
    · intro a ha
      obtain ⟨he,hh⟩ := h.2.2.2 a ha
      rw [← he]; exact ⟨e.symm_apply_apply _,ih hh⟩

theorem Agree.place (h : Q.Agree Q' f p (R+1) i) : Q.w.place i = Q'.w.place (f i) := congrArg (· / 3) h.1

theorem Agree.shore (h : Q.Agree Q' f p (R+1) i) (d : Bool) : Q.w.Shore d i ↔ Q'.w.Shore d (f i) := by
  simp only [Shore,h.1]

theorem Agree.num (h : Q.Agree Q' f p (R+1) i) (d : Bool) : Q.w.num d i = Q'.w.num d (f i) := by
  simp only [Board.num,loc,h.1]

def Fits (Q : Network u X) (p : ℕ) (r : Q.w.Round) :=
  ∀ i d j, r.jump i d j → ∃ a, u.phase a < p ∧ d = !(u.side a) ∧ Q.slot a i = j

theorem Fits.refine {r : Q.w.Round} (h : Q.Fits p r) {a : u.Ticket} (ha : u.phase a < p) (P : X → Prop) :
    Q.Fits p (Q.refine r a P) := by
  rintro i d j (hh | ⟨he,hj,_⟩)
  · exact h _ _ _ hh
  · exact ⟨a,ha,he,hj⟩

structure Matches (Q : Network u X) (Q' : Network u Y) (e : X ≃ Y) (p R : ℕ)
    (r : Q.w.Round) (r' : Q'.w.Round) : Prop where
  fits : Q.Fits p r
  fits' : Q'.Fits p r'
  mark : ∀ i, Q.Agree Q' e p R i → ∀ d, r.mark i d ↔ r'.mark (e i) d
  jump : ∀ i, Q.Agree Q' e p R i → ∀ d j, r.jump i d j ↔ r'.jump (e i) d (e j)

namespace Matches

variable {e : X ≃ Y} {r : Q.w.Round} {r' : Q'.w.Round} (m : Q.Matches Q' e p R r r')

theorem first : Q.Matches Q' e p 1 Q.first Q'.first :=
  ⟨fun _ _ _ h => h.elim,fun _ _ _ h => h.elim,fun _ h _ => by simp [Network.first,Middle,h.1,h.2.1],by simp [Network.first]⟩

include m

theorem symm : Q'.Matches Q e.symm p R r' r := by
  refine ⟨m.fits',m.fits,?_,?_⟩
  · intro i h d; simpa using (m.mark _ h.symm d).symm
  · intro i h d j; simpa using (m.jump _ h.symm d (e.symm j)).symm

theorem up (h : R ≤ S) : Q.Matches Q' e p S r r' :=
  ⟨m.fits,m.fits',fun i hi => m.mark i (hi.cut h),fun i hi => m.jump i (hi.cut h)⟩

theorem refine {a : u.Ticket} (ha : u.phase a < p) {P : X → Prop} {P' : Y → Prop}
    (hP : ∀ i, Q.Agree Q' e p S i → (P i ↔ P' (e i))) (hle : R ≤ S+2) :
    Q.Matches Q' e p (S+2) (Q.refine r a P) (Q'.refine r' a P') := by
  refine ⟨m.fits.refine ha P,m.fits'.refine ha P',?_,?_⟩
  · intro i h d
    have hm := m.mark _ (h.cut hle) d
    by_cases hc : r.mark i d
    swap
    · simp [Network.refine,hc,mt hm.mpr hc]
    have hs := h.2.2.2 a ha
    simp only [Network.refine,hc,hm.mp hc,true_and]
    split
    · obtain ⟨he,hh⟩ := h.2.2.1 d (r.middle _ _ hc).2
      rw [← he]; exact hP _ (hh.cut (Nat.le_succ _))
    · rw [← hs.1,← hs.2.2.1]
      by_cases hl : Q.w.live (Q.slot a i)
      · obtain ⟨he,hh⟩ := hs.2.2.2.1 (u.side a) hl
        rw [← he,hP _ hh]
      · simp [hl]
  · intro i h d j
    simp only [Network.refine,← (h.2.2.2 a ha).1,e.injective.eq_iff,ne_eq,m.jump _ (h.cut hle)]

theorem step {d : Bool} {j : X} (hm : r.Move i d j) (h : Q.Agree Q' e p (S+1) i) (hR : R ≤ S+1) :
    r'.Move (e i) d (e j) ∧ Q.Agree Q' e p S j := by
  rcases hm with ⟨hl,rfl | hj⟩
  · exact ⟨⟨h.2.1.mp hl,.inl (h.2.2.1 d hl).1⟩,(h.2.2.1 d hl).2⟩
  obtain ⟨a,ha,_,he⟩ := m.fits _ _ _ hj
  exact ⟨⟨h.2.1.mp hl,.inr ((m.jump _ (h.cut hR) _ _).mp hj)⟩,he ▸ (h.2.2.2 a ha).2⟩

end Matches
end OAI.Geometry.Hirsch.Layer.Board.Network
