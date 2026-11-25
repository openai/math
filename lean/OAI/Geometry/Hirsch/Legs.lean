import OAI.Geometry.Hirsch.Compressed

noncomputable section

namespace OAI.Geometry.Hirsch.Layer.World

open Board

variable {X : Type} {n : ℕ} (w : World X n) (width : ℕ)

inductive Leg (d : Bool) : X → X → Prop
  | here {x} (hm : ¬w.Blank width x) : Leg d x x
  | go {x y} (hm : ¬w.Blank width x) (hl : w.live x) (ht : Leg d (w.step x d) y) : Leg d x y

variable {w width} {x y : X} {d : Bool}

theorem Leg.info (h : w.Leg width d x y) : ¬w.Blank width x ∧ ¬w.Blank width y ∧
    w.block width y = w.block width x ∧ w.finish width d y = w.finish width d x ∧
    (y = x ∨ w.rank y < w.rank x) := by
  induction h with
  | here hm => exact ⟨hm,hm,rfl,rfl,.inl rfl⟩
  | go hm hl ht ih =>
    obtain ⟨_,hy,hb,he,hr⟩ := ih
    refine ⟨hm,hy,hb.trans (w.same_step hl hm d),?_,.inr ?_⟩
    · exact he.trans (by conv_rhs => rw [finish,ite_eq_right hm,dite_eq_left hl])
    · exact (hr.elim (fun h => (congrArg w.rank h).le) LT.lt.le).trans_lt (w.decrease _ hl d)

variable (w width) (base : ℕ) (hw : 3 ≤ width) (hb : 0 < base)

theorem at_real (x : X) : (w.board width base hw hb).place (.inl x) = w.index width base x := by
  change w.height width base (.inl x)/3 = _
  rw [w.height_real]; have := w.offset_small width x; omega

theorem mid_real (x : X) : (w.board width base hw hb).Middle (.inl x) ↔ ¬w.Blank width x := by
  change w.height width base (.inl x)%3 = 1 ↔ _
  rw [w.height_real,← w.offset_mid]
  have := w.offset_small width x; omega

theorem shore_real (hm : w.Blank width x) : ∃ d, (w.board width base hw hb).Shore d (.inl x) := by
  have hh := (w.mid_real width base hw hb x).not.mpr (not_not.mpr hm)
  unfold Middle at hh
  by_cases h : (w.board width base hw hb).layer (.inl x)%3 = 2
  · exact ⟨true,h⟩
  · exact ⟨false,by unfold Shore; simp; omega⟩

def along : Compressed X → Bool → Compressed X → Prop
  | .inl x,d,.inl y => w.Leg width d x y
  | _,_,_ => False

variable {u : Dials}

def legs (v : u.Valid) (hw : 3 ≤ width) : Board.Legs u (Compressed X) where
  w := w.board width (u.a^u.h) hw (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) v.base) _)
  along := w.along width
  info := by
    rintro (x | x) d (y | y) h <;> try exact h.elim
    obtain ⟨hx,hy,he,hf,hr⟩ := Leg.info h
    refine ⟨(w.mid_real ..).mpr hx,.inl hx,.inl hy,?_,?_,?_⟩
    · change w.height width (u.a^u.h) (.inl y) = w.height width (u.a^u.h) (.inl x)
      rw [height_real,height_real,(w.offset_mid _ _).mpr hx,(w.offset_mid _ _).mpr hy]
      simp only [index,he]
    · simpa only [board,dest,ite_eq_right hx,ite_eq_right hy] using hf
    · exact hr.imp (congrArg Sum.inl) Nat.succ_lt_succ

def Allowed (occ : X → Prop) (par site : ℕ) (i : X) :=
  w.block (width*base) i = par ∧ (occ i → w.index width base i = site)

def Stop (i : X) := ¬w.live i ∨ w.Blank (width*base) i

def Resume (occ : X → Prop) (par site : ℕ) (d : Bool) (k : ℕ) : Compressed X → Prop
  | .inl i => w.block (width*base) i = par →
      w.Walk (w.Allowed width base occ par site) (w.Stop width base) i d k
  | .inr _ => True

def Permitted (occ : X → Prop) (site : ℕ) (d : Bool) (x : X) :=
  ∀ y, w.Leg width d x y → occ y → w.index width base y = site

variable {w width base} {occ : X → Prop} {par site k : ℕ}

theorem Permitted.next (h : w.Permitted width base occ site d x) (hm : ¬w.Blank width x) (hl : w.live x) :
    w.Permitted width base occ site d (w.step x d) := fun _ ht => h _ (.go hm hl ht)

theorem Leg.expand (h : w.Leg width d x y) (ok : w.Permitted width base occ site d x)
    (ht : w.Resume width base occ par site d k (.inl y)) : w.Resume width base occ par site d k (.inl x) := by
  induction h with
  | here => exact ht
  | go hm hl h ih =>
    intro hp
    have hp' := (w.same_step hl (fun hh => hm (w.blank_mono (dvd_mul_right ..) hh)) d).trans hp
    exact .go ⟨hp,ok _ (.here hm)⟩ hl (by simp [turn]) (ih (ok.next hm hl) ht hp')

theorem expand_finish (w : World X n) (d : Bool) : ∀ x, w.Permitted width base occ site d x →
    w.Resume width base occ par site d k (w.finish width d x) → w.Resume width base occ par site d k (.inl x) := by
  apply w.induct
  intro x ih ok ht
  rw [finish] at ht
  split at ht
  · exact ht
  rename_i hm
  intro hp
  have good : w.Allowed width base occ par site x := ⟨hp,ok _ (.here hm)⟩
  split at ht
  · rename_i hl
    have hp' := (w.same_step hl (fun hh => hm (w.blank_mono (dvd_mul_right ..) hh)) d).trans hp
    exact .go good hl (by simp [turn]) (ih hl d (ok.next hm hl) ht hp')
  · exact .done good (.inl ‹_›)

theorem expand_dest (blank : ∀ x, w.Blank width x → ¬occ x) (hl : w.awake width base (.inl x))
    (ok : w.Permitted width base occ site d x) (ht : w.Resume width base occ par site d k (w.dest width (.inl x) d)) :
    w.Resume width base occ par site d k (.inl x) := by
  rw [dest] at ht
  split at ht
  · rename_i hb
    obtain ⟨hl,hn⟩ := hl.resolve_left (not_not.mpr hb)
    intro hp
    exact .go ⟨hp,fun h => (blank _ hb h).elim⟩ hl (by simp [turn]) (ht ((w.same_step hl hn d).trans hp))
  · exact w.expand_finish d _ ok ht

end OAI.Geometry.Hirsch.Layer.World
