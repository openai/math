import OAI.Geometry.Hirsch.Tracks

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {I : Type} [Fintype I] {Q Q' : Network u I} {e : Equiv.Perm I}
  {p k : ℕ} (v : u.Valid)

theorem tracks (hk : k ≤ u.h) (hp : 2*k ≤ p) (c : u.History k) :
    Tracks e p (Q.process v k hk c) (Q'.process v k hk c) := by
  induction k with
  | zero =>
    refine ⟨⟨rfl,v.invariant e,v.atom_same e 0⟩,Matches.first,?_⟩
    intro i _ x
    simp only [process,Coins.Rules.mem,Coins.Rules.initial,Coins.All,Finset.notMem_empty,IsEmpty.forall_iff,
      implies_true,and_true]
    exact v.atom_same e 0 _ _
  | succ k ih =>
    obtain ⟨⟨c,s⟩,b⟩ := c
    exact (ih (by omega) (by omega) c).succ (by omega) s b (by omega)

def window (u : Dials) := radius u (u.h+1)

theorem window_pos (u : Dials) : 0 < window u := by unfold window; rw [radius]; omega

theorem local_want (a : u.Ticket) {i : I} (h : Q.Agree Q' e (u.phase a) (window u) i) :
    Q.want v a i ↔ Q'.want v a (e i) := by
  obtain ⟨⟨k,hk⟩,⟨c,s⟩,b⟩ := a
  have hr : radius u (k+1) ≤ window u := radius_mono u (by omega)
  rw [radius] at hr
  cases b with
  | none =>
    have g := tracks (Q := Q) (Q' := Q') (e := e) v hk.le (le_refl (2*k)) c
    have eq := g.scale hk (h.cut (show checkRadius u k+reach u k ≤ window u by unfold checkRadius; omega))
    simp only [want,eq]
  | some b =>
    have g := tracks (Q := Q) (Q' := Q') (e := e) v hk.le (Nat.le_succ (2*k)) c
    have eq := g.pick hk s (by omega) (h.cut (show midRadius u k+reach u k ≤ window u by
      unfold midRadius checkRadius; omega))
    simp only [want,eq]

theorem local_pass (c : u.History u.h) {i : I} (h : Q.Agree Q' e (2*u.h) (window u) i)
    (x : Table (u.Cell I)) : Q.passes v c x i ↔ Q'.passes v c (u.tables e x) (e i) :=
  (tracks v le_rfl le_rfl c).checked _ (h.cut (by unfold window checkRadius; rw [radius]; omega)) x

theorem final_fits (Q : Network u I) (c : u.History u.h) : Q.Fits (2*u.h) (Q.done v c).round :=
  (tracks (Q := Q) (Q' := Q) (e := Equiv.refl I) v le_rfl le_rfl c).round.fits

def Enrolled (u : Dials) : ∀ k, u.History k → u.Ticket → Prop
  | 0,_,_ => False
  | k+1,c,a => Enrolled u k c.1.1 a ∨ ∃ hk : k < u.h,
      a = u.ticket hk c.1.1 c.1.2 none ∨ a = u.ticket hk c.1.1 c.1.2 (some c.2)

theorem color (Q : Network u I) (key : Bool → I) (k : ℕ) (hk : k ≤ u.h) :
    ∃ c : u.History k, ∀ a, Enrolled u k c a → Q.want v a (key (u.side a)) := by
  induction k with
  | zero => exact ⟨(),fun _ h => h.elim⟩
  | succ k ih =>
    obtain ⟨c,hc⟩ := ih (by omega)
    have h : k < u.h := by omega
    let g := Q.process v k h.le c
    let i := key (u.east k c)
    let s := g.stage.scale v h i
    let b := g.stage.pick v h (g.mid h s) i
    refine ⟨((c,s),b),?_⟩
    rintro a (ha | ⟨_,rfl | rfl⟩)
    · exact hc _ ha
    · rfl
    · rfl

def accepts (Q : Network u I) (v : u.Valid) (a : u.Ticket) (i : I) (d : Bool) :=
  if d = u.side a then Q.want v a (Q.w.step i d)
  else Q.w.live (Q.slot a i) ∧ Q.want v a (Q.w.step (Q.slot a i) (u.side a))

theorem marks (Q : Network u I) {i : I} {d : Bool} (hi : Q.w.Middle i) (hl : Q.w.live i)
    (k : ℕ) (hk : k ≤ u.h) (c : u.History k)
    (ha : ∀ a, Enrolled u k c a → Q.accepts v a i d) : (Q.process v k hk c).round.mark i d := by
  induction k with
  | zero => exact ⟨hi,hl⟩
  | succ k ih =>
    have h : k < u.h := by omega
    exact ⟨⟨ih h.le c.1.1 (fun a h => ha a (.inl h)),ha _ (.inr ⟨h,.inl rfl⟩)⟩,
      ha _ (.inr ⟨h,.inr rfl⟩)⟩

end OAI.Geometry.Hirsch.Layer.Board.Network
