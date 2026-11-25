import OAI.Geometry.Hirsch.Stock

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

structure Network (u : Dials) (I : Type) where
  w : Board I (u.a^u.h)
  slot : u.Ticket → I → I
  same : ∀ a i, w.layer (slot a i) = w.layer i
  jump : ∀ a i, slot a i ≠ i → w.live i ∧ w.rank (slot a i) < w.rank i

namespace Network

variable {u : Dials} {I : Type} (Q : Network u I)

def first : Q.w.Round where
  mark i _ := Q.w.Middle i ∧ Q.w.live i
  middle _ _ h := h
  jump _ _ _ := False
  localJump _ _ _ h := h.elim

def refine (r : Q.w.Round) (a : u.Ticket) (P : I → Prop) : Q.w.Round where
  mark i e := r.mark i e ∧ (if e = u.side a then P (Q.w.step i e)
    else Q.w.live (Q.slot a i) ∧ P (Q.w.step (Q.slot a i) (u.side a)))
  middle i e h := r.middle i e h.1
  jump i e j := r.jump i e j ∨ e = !(u.side a) ∧ Q.slot a i = j ∧ j ≠ i
  localJump := by
    rintro i e j (h | ⟨_,rfl,hn⟩)
    · exact r.localJump _ _ _ h
    · exact ⟨(Q.jump a i hn).1,Q.same a i,(Q.jump a i hn).2⟩

theorem finer (r : Q.w.Round) (a : u.Ticket) (P : I → Prop) : (Q.refine r a P).Finer r :=
  ⟨fun _ _ h => h.1,fun _ _ _ h => .inl h⟩

theorem links (r : Q.w.Round) (a : u.Ticket) (P : I → Prop) :
    (Q.refine r a P).Links (u.side a) P := by
  constructor
  · intro i h; simpa [refine] using h.2
  intro i h
  have hh : Q.w.live (Q.slot a i) ∧ P (Q.w.step (Q.slot a i) (u.side a)) := by simpa using h.2
  have hmid := (r.middle _ _ h.1).1
  refine ⟨Q.slot a i,?_,by simpa [Board.Middle,Q.same] using hmid,hh⟩
  by_cases he : Q.slot a i = i
  · exact .inl he
  · exact .inr (.inr ⟨rfl,rfl,he⟩)

variable [Fintype I] (v : u.Valid)

structure Process (k : ℕ) (c : u.History k) where
  raw : (v.coin (I := I)).Raw I
  rule : Coins.Rules raw
  round : Q.w.Round
  stage : Board.Stage u.stamp u k rule round (u.east k c)

namespace Process

variable {Q v} {k : ℕ} {c : u.History k} (g : Q.Process v k c) (hk : k < u.h) (s : u.Scale) (b : u.Bin)

def mid := Q.refine g.round (u.ticket hk c s none) (fun i => g.stage.scale v hk i = s)

def last := Q.refine (g.mid hk s) (u.ticket hk c s (some b)) (fun i => g.stage.pick v hk (g.mid hk s) i = b)

def succ : Q.Process v (k+1) ((c,s),b) where
  raw := g.raw.join (v.fresh hk) ((v.fresh_tag hk).separate g.stage.view)
  rule := g.stage.advance v hk (v.foil hk g.stage.rate) (v.fresh_tag hk) (g.mid hk s)
  round := g.last hk s b
  stage := g.stage.next v hk _ _ rfl le_rfl (Q.finer ..) (Q.finer ..) (Q.links ..) (Q.links ..)

def checked := Board.Stage.screened u k g.rule g.round (u.east k c)

end Process

def process : ∀ k, k ≤ u.h → (c : u.History k) → Q.Process v k c
  | 0,_,_ => ⟨v.atom 0,Coins.Rules.initial _,Q.first,Board.Stage.initial v (v.tagged 0) rfl _ _⟩
  | k+1,hk,c => (process k (by omega) c.1.1).succ (by omega) c.1.2 c.2

def want (a : u.Ticket) (i : I) :=
  let hk := a.1.isLt
  let g := Q.process v a.1.val hk.le a.2.1.1
  match a.2.2 with
  | none => g.stage.scale v hk i = a.2.1.2
  | some b => g.stage.pick v hk (g.mid hk a.2.1.2) i = b

def done (c : u.History u.h) := Q.process v u.h le_rfl c

def passes (c : u.History u.h) (x : Table (u.Cell I)) (i : I) := i ∈ (Q.done v c).checked.pass x

theorem pair (c : u.History u.h) {i j : I} (hi : Q.w.place i = Q.w.place j) (hne : i ≠ j) :
    u.gamma*(u.rate u.h)^2 ≤ v.coin.law.prob (fun x => Q.passes v c x i ∧ Q.passes v c x j) := by
  let g := Q.done v c
  have card : ({i,j} : Finset I).card = 2 := by simp [hne]
  have hh := (g.stage.checked v).passage (s := {i,j}) (card.le.trans v.keys) (by
    intro k hk; left; intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk hl
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> simp [hi]) (v.reliable _ le_rfl)
  change u.gamma*g.raw.rate^({i,j} : Finset I).card ≤ _ at hh
  rw [g.stage.rate,card] at hh
  exact hh.trans (v.coin.law.mono fun _ h => ⟨h (by simp),h (by simp)⟩)

end Network
end OAI.Geometry.Hirsch.Layer.Board
