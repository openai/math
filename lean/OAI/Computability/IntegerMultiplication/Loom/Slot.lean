import OAI.Computability.IntegerMultiplication.Strip.Adopt
import OAI.Computability.IntegerMultiplication.Strip.Dims

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims
variable {A F T U C : Type} {D P R S B : Tape}
variable {a : Series A} {f : Series F} {t : Series T} {u : Series U} {c : Series C}

/-! Change of flat physical key to a run of variable-width fields,
with Dims segments on both sides. Adopt ensures tabulation byte-compatible.
Explicit Lens accessors make logic independent of any layout compatibility
assumptions. Insert/remove/tune one and two identical fields. -/
abbrev Board (P : Tape) (t : Series T) (S : Tape) := (layout P).cart (t.cart (layout S))
abbrev Path (P : Tape) (t : Series T) (R : Tape) (u : Series U) (S : Tape) :=
  (layout P).cart (t.cart (Board R u S))
abbrev Seal (s : Series A) (P : Tape) := Adopt s (layout P)

def unite (p r : Tape) : Seal ((layout p).cart (layout r)) (p++r) :=
  ⟨Union p r,fun {_} => tab_cat p r⟩

structure Slot (a : Series A) (P : Tape) (t : Series T) (S : Tape) where
  view : Adopt a (Board P t S)
structure Axis (a : Series A) (P : Tape) (t : Series T) (R : Tape) (u : Series U) (S : Tape) where
  view : Adopt a (Path P t R u S)

namespace Slot
def read (e : Slot a P t S) (x : A) : T := (e.view.cast x).2.1
def alter (e : Slot a P t S) (x : A) (v : T) : A :=
  let w := e.view.cast x
  e.view.cast.symm (w.1,v,w.2.2)
@[simp] theorem changed (e : Slot a P t S) (x : A) (v : T) :
    e.view.cast (e.alter x v) = ((e.view.cast x).1,v,(e.view.cast x).2.2) := by
  simp [alter]
@[simp] theorem fetch (e : Slot a P t S) (x : A) (v : T) :
    e.read (e.alter x v) = v := by simp [read]
@[simp] theorem recover (e : Slot a P t S) (x : A) :
    e.alter x (e.read x) = x := by apply e.view.cast.injective; simp [read]
@[simp] theorem later (e : Slot a P t S) (x : A) (v w : T) :
    e.alter (e.alter x v) w = e.alter x w := by
  apply e.view.cast.injective; simp

def tune (e : Slot a P t S) (d : T≃T) : A≃A where
  toFun x := e.alter x (d (e.read x))
  invFun x := e.alter x (d.symm (e.read x))
  left_inv _ := by simp
  right_inv _ := by simp

def arrive (e : Slot a P t S) (h : Adopt f a) : Slot f P t S :=
  ⟨h.thenDo e.view⟩
theorem pull (e : Slot a P t S) (h : Adopt f a) (x) :
    (e.arrive h).read x = e.read (h.cast x) := rfl
@[simp] theorem endorse (e : Slot a P t S) (h : Adopt f a) (x) (y) :
    h.cast ((e.arrive h).alter x y) = e.alter (h.cast x) y := by
  dsimp only [arrive,alter, Adopt.thenDo,Equiv.trans_apply,Equiv.symm_trans_apply]
  simp

def sole (t : Series T) : Slot t [] t [] :=
  ⟨((Adopt.skip _).back.thenDo (Adopt.omitL _).back)⟩
@[simp] theorem sole_check (t : Series T) (x) : (sole t).read x=x := rfl
@[simp] theorem sole_exchange (t : Series T) (x y) : (sole t).alter x y=y := rfl

/-- Product with an earlier complete region. -/
def enter (e : Slot a P t S) (q : Seal f D) :
    Slot (f.cart a) (D++P) t S :=
  let h := q.split e.view
  let j := (Adopt.rotate (layout D) (layout P) (t.cart (layout S))).back
  ⟨(h.thenDo j).thenDo ((unite D P).split (Adopt.same _))⟩
@[simp] theorem enter_read (e : Slot a P t S) (q : Seal f D) (i x) :
    (e.enter q).read (i,x)=e.read x := rfl
@[simp] theorem enter_alter (e : Slot a P t S) (q : Seal f D) (i x v) :
    (e.enter q).alter (i,x) v = (i,e.alter x v) := by
  apply (e.enter q).view.cast.injective
  rw [changed]
  change
    (Union D P (q.cast i,(e.view.cast x).1),v,(e.view.cast x).2.2) =
    (Union D P (q.cast i,(e.view.cast (e.alter x v)).1),
      (e.view.cast (e.alter x v)).2)
  simp

def exit (e : Slot a P t S) (q : Seal f D) :
    Slot (a.cart f) P t (S++D) :=
  let h := e.view.split q
  let j := Adopt.rotate (layout P) (t.cart (layout S)) (layout D)
  let k := (Adopt.rotate t (layout S) (layout D)).thenDo
    ((Adopt.same t).split (unite S D))
  ⟨(h.thenDo j).thenDo ((Adopt.same _).split k)⟩
@[simp] theorem exit_read (e : Slot a P t S) (q : Seal f D) (i x) :
    (e.exit q).read (x,i) = e.read x := rfl
@[simp] theorem exit_alter (e : Slot a P t S) (q : Seal f D) (i x v) :
    (e.exit q).alter (x,i) v = (e.alter x v,i) := by
  apply (e.exit q).view.cast.injective
  rw [changed]
  change ((e.view.cast x).1,v,Union S D ((e.view.cast x).2.2,q.cast i)) =
    ((e.view.cast (e.alter x v)).1,(e.view.cast (e.alter x v)).2.1,
      Union S D ((e.view.cast (e.alter x v)).2.2,q.cast i))
  simp
end Slot

namespace Axis
variable {E : Axis a P t R u S}
def pair (e : Axis a P t R u S) (x : A) : T × U :=
  let v := (e.view.cast x).2
  (v.1,v.2.2.1)
def bridge (e : Axis a P t R u S) (x : A) (v : T × U) : A :=
  let w := e.view.cast x
  e.view.cast.symm (w.1,v.1,w.2.2.1,v.2,w.2.2.2.2)
@[simp] theorem changed (e : Axis a P t R u S) (x : A) (v) :
    e.view.cast (e.bridge x v) =
      ((e.view.cast x).1,v.1,(e.view.cast x).2.2.1,v.2,(e.view.cast x).2.2.2.2) := by
  simp [bridge]
@[simp] theorem fetch (e : Axis a P t R u S) (x : A) (v) :
    e.pair (e.bridge x v) = v := by simp [pair]
@[simp] theorem recover (e : Axis a P t R u S) (x) :
    e.bridge x (e.pair x)=x := by apply e.view.cast.injective; simp [pair]
@[simp] theorem later (e : Axis a P t R u S) (x v w) :
    e.bridge (e.bridge x v) w = e.bridge x w := by apply e.view.cast.injective; simp
def tune (e : Axis a P t R u S) (d : (T × U) ≃ (T × U)) : A ≃ A where
  toFun x := e.bridge x (d (e.pair x))
  invFun x := e.bridge x (d.symm (e.pair x))
  left_inv _ := by simp
  right_inv _ := by simp

def arrive (e : Axis a P t R u S) (h : Adopt f a) : Axis f P t R u S :=
  ⟨h.thenDo e.view⟩
theorem pull (e : Axis a P t R u S) (h : Adopt f a) (x) :
    (e.arrive h).pair x = e.pair (h.cast x) := rfl
@[simp] theorem endorse (e : Axis a P t R u S) (h : Adopt f a) (x) (y) :
    h.cast ((e.arrive h).bridge x y) = e.bridge (h.cast x) y := by
  dsimp only [arrive,bridge, Adopt.thenDo,Equiv.trans_apply,Equiv.symm_trans_apply]
  simp
def both (e : Slot a P t R) (q : Slot f D u S) :
    Axis (a.cart f) P t (R++D) u S :=
  let h := e.view.split q.view
  let j := Adopt.rotate (layout P) (t.cart (layout R)) (Board D u S)
  let k := Adopt.rotate t (layout R) (Board D u S)
  let g := (Adopt.rotate (layout R) (layout D) (u.cart (layout S))).back.thenDo
    ((unite R D).split (Adopt.same _))
  ⟨(h.thenDo j).thenDo ((Adopt.same _).split (k.thenDo ((Adopt.same _).split g)))⟩
@[simp] theorem both_pair (e : Slot a P t R) (q : Slot f D u S) (x y) :
    (both e q).pair (x,y) = (e.read x,q.read y) := rfl
@[simp] theorem both_bridge (e : Slot a P t R) (q : Slot f D u S) (x y j k) :
    (both e q).bridge (x,y) (j,k) = (e.alter x j, q.alter y k) := by
  apply (both e q).view.cast.injective
  have key (x : A) (y : F) : (both e q).view.cast (x,y) =
      ((e.view.cast x).1,(e.view.cast x).2.1,
       Union R D ((e.view.cast x).2.2,(q.view.cast y).1),(q.view.cast y).2) := rfl
  rw [changed,key,key]; simp

def enter (e : Axis a P t R u S) (q : Seal f D) :
    Axis (f.cart a) (D++P) t R u S :=
  let h := q.split e.view
  let j := (Adopt.rotate (layout D) (layout P) (t.cart (Board R u S))).back
  ⟨(h.thenDo j).thenDo ((unite D P).split (Adopt.same _))⟩
@[simp] theorem enter_pair (e : Axis a P t R u S) (q : Seal f D) (i x) :
    (e.enter q).pair (i,x)=e.pair x := rfl
@[simp] theorem enter_bridge (e : Axis a P t R u S) (q : Seal f D) (i x v) :
    (e.enter q).bridge (i,x) v = (i,e.bridge x v) := by
  apply (e.enter q).view.cast.injective
  have key (x : F) (y : A) : (e.enter q).view.cast (x,y) =
      (Union D P (q.cast x,(e.view.cast y).1),(e.view.cast y).2) := rfl
  rw [changed,key,key]; simp

def exit (e : Axis a P t R u S) (q : Seal f D) :
    Axis (a.cart f) P t R u (S++D) :=
  let h := e.view.split q
  let j := Adopt.rotate (layout P) (t.cart (Board R u S)) (layout D)
  let k := Adopt.rotate t (Board R u S) (layout D)
  let g := Adopt.rotate (layout R) (u.cart (layout S)) (layout D)
  let b := (Adopt.rotate u (layout S) (layout D)).thenDo ((Adopt.same _).split (unite S D))
  ⟨(h.thenDo j).thenDo
    ((Adopt.same _).split (k.thenDo ((Adopt.same _).split (g.thenDo ((Adopt.same _).split b)))))⟩
@[simp] theorem exit_pair (e : Axis a P t R u S) (q : Seal f D) (i x) :
    (e.exit q).pair (x,i)=e.pair x := rfl
@[simp] theorem exit_bridge (e : Axis a P t R u S) (q : Seal f D) (i x v) :
    (e.exit q).bridge (x,i) v = (e.bridge x v,i) := by
  apply (e.exit q).view.cast.injective
  have key (x : A) (y : F) : (e.exit q).view.cast (x,y) =
      ((e.view.cast x).1,(e.view.cast x).2.1,(e.view.cast x).2.2.1,(e.view.cast x).2.2.2.1,
       Union S D ((e.view.cast x).2.2.2.2,q.cast y)) := rfl
  rw [changed,key,key]; simp
end Axis
end Loom

end IntegerMultiplication
end Computability
end OAI
