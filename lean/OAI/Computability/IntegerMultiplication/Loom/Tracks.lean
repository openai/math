import OAI.Computability.IntegerMultiplication.Loom.Slot
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims
variable {X : Type} (x : Series X) {i j n : ℕ}
/-- n repeats of X chunk, first most significant. -/
private def emptyVec (X : Type) : Unit ≃ (Fin 0 → X) where
  toFun _ := Fin.elim0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _f := funext fun j => j.elim0
def Track : (n : ℕ) → Series (Fin n → X)
| 0 => Series.one.via (emptyVec X)
| n+1 => (x.cart (Track n)).via (Fin.consEquiv (fun _:Fin (n+1) => X))
abbrev join {n} := (Fin.consEquiv (fun _ => X) : X × (Fin n → X) ≃ _)
@[simp] theorem first_j (f : X) (g : Fin n → X) :
    join (f,g) 0 = f := by simp only [join,Fin.consEquiv_apply]; rfl
@[simp] theorem tail_j (f : X) (g : Fin n → X) (i : Fin n) :
    join (f,g) i.succ = g i := by simp [join,Fin.consEquiv_apply]
@[simp] theorem leave (f : Fin (n+1) → X) :
    join.symm f = (f 0,fun i : Fin n => f i.succ) := rfl
def step (n : ℕ) : Adopt (Track x (n+1)) (x.cart (Track x n)) := ((Adopt.turn _ join).back)

def Rack (d : Tape) : ℕ → Tape
| 0 => []
| n+1 => d++Rack d n
@[simp] theorem pieces (d : Tape) (n) : (Rack d n).length = d.length*n := by
  induction n with
  | zero => simp [Rack]
  | succ n ih => simp [Rack,ih, Nat.mul_add]; omega

def park (d : Tape) (e : Seal x d) :
    (n : ℕ) → Seal (Track x n) (Rack d n)
| 0 => (Adopt.turn _ (emptyVec X)).back
| n+1 => ((step x n).thenDo (e.split (park d e n))).thenDo (unite d _)

structure Single (d : Tape) (n : ℕ) (i : Fin n) where
  before : ℕ
  after : ℕ
  shape : Slot (Track x n) (Rack d before) x (Rack d after)
  size : before+after+1=n
  pos : before=i.val
  who w : shape.read w=w i
  put w v : shape.alter w v=Function.update w i v
structure Double (d : Tape) (n : ℕ) (i j : Fin n) where
  before : ℕ
  middle : ℕ
  after : ℕ
  shape : Axis (Track x n) (Rack d before) x (Rack d middle) x (Rack d after)
  size : before+middle+after+2=n
  pos : before=i.val
  through : before+middle+1=j.val
  who w : shape.pair w=(w i,w j)
  put w v : shape.bridge w v=Function.update (Function.update w i v.1) j v.2

private theorem edit0 (f : X) (g : Fin n → X) (w : X) :
    join (w,g) = Function.update (join (f,g)) 0 w := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i
  · simp
  simp
private theorem editT (f : X) (g : Fin n → X) (w : X) (i : Fin n) :
    join (f,Function.update g i w) = Function.update (join (f,g)) i.succ w := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [Function.update_of_ne (Ne.symm i.succ_ne_zero)]
  by_cases h : j=i
  · simp [h]
  have e : j.succ≠i.succ := fun g => h (Fin.succ_inj.mp g)
  simp [h,e]
def first (d : Tape) (e : Seal x d) (n : ℕ) : Single x d (n+1) 0 :=
  let h := ((Slot.sole x).exit (park x d e n)).arrive (step x n)
  { before := 0
    after := n
    shape := h
    size := by simp
    pos := rfl
    who w := by change (((Slot.sole x).exit (park x d e n)).arrive (step x n)).read w = _; exact Slot.pull _ _ _
    put w v := by
      obtain ⟨⟨m,u⟩,rfl⟩ := join.surjective w
      rw [← edit0]
      apply (step x n).cast.injective
      change (step x n).cast ((((Slot.sole x).exit (park x d e n)).arrive (step x n)).alter (join (m,u)) v) = _
      rw [Slot.endorse]
      change ((Slot.sole x).exit _).alter (join.symm (join (m,u))) v = join.symm (join (v,u))
      simp only [Equiv.symm_apply_apply,Slot.exit_alter,Slot.sole_exchange] }
def later (d : Tape) (e : Seal x d) (i : Fin n) (l : Single x d n i) :
    Single x d (n+1) i.succ :=
  let h := (l.shape.enter e).arrive (step x n)
  { before := l.before+1
    after := l.after
    shape := h
    size := by have := l.size; omega
    pos := by rw [l.pos]; rfl
    who w := by
      change ((l.shape.enter e).arrive (step x n)).read w = _; rw [Slot.pull]; change (l.shape.enter e).read (w 0,fun i : Fin n => w i.succ) = _
      rw [Slot.enter_read,l.who]
    put w v := by
      obtain ⟨⟨m,u⟩,rfl⟩ := join.surjective w
      rw [← editT]
      apply (step x n).cast.injective
      change (step x n).cast (((l.shape.enter e).arrive (step x n)).alter (join (m,u)) v) = _
      rw [Slot.endorse]
      change (l.shape.enter e).alter (join.symm (join (m,u))) v = join.symm (join (m,_))
      simp only [Equiv.symm_apply_apply,Slot.enter_alter,l.put] }

def pick (d : Tape) (e : Seal x d) : {n : ℕ} → (i : Fin n) → Single x d n i
| 0,i => i.elim0
| n+1,i => Fin.cases (first x d e n) (fun j => later x d e j (pick d e j)) i

def firstTwo (d : Tape) (j : Fin n)
    (q : Single x d n j) :
    Double x d (n+1) 0 j.succ :=
  let h := (Axis.both (Slot.sole x) q.shape).arrive (step x n)
  { before := 0
    middle := q.before
    after := q.after
    shape := h
    size := by have := q.size; omega
    pos := rfl
    through := by simp [q.pos]
    who w := by
      change ((Axis.both (Slot.sole x) q.shape).arrive (step x n)).pair w = _; rw [Axis.pull]; change (Axis.both _ _).pair (w 0,fun i:Fin n => w i.succ) = _
      rw [Axis.both_pair,Slot.sole_check,q.who]
    put w v := by
      obtain ⟨⟨m,u⟩,rfl⟩ := join.surjective w
      obtain ⟨a,b⟩ := v
      rw [← edit0,← editT]
      apply (step x n).cast.injective
      change (step x n).cast (((Axis.both (Slot.sole x) q.shape).arrive (step x n)).bridge (join (m,u)) (a,b)) = _
      rw [Axis.endorse]
      change (Axis.both _ _).bridge (join.symm (join (m,u))) (a,b) = join.symm (join (a,_))
      simp only [Equiv.symm_apply_apply,Axis.both_bridge,Slot.sole_exchange,q.put] }

def laterTwo (d : Tape) (e : Seal x d) (i j : Fin n)
    (q : Double x d n i j) :
    Double x d (n+1) i.succ j.succ :=
  let h := (q.shape.enter e).arrive (step x n)
  { before := q.before+1
    middle := q.middle
    after := q.after
    shape := h
    size := by have := q.size; omega
    pos := by rw [q.pos]; rfl
    through := by simp only [Fin.val_succ]; have := q.through; omega
    who w := by
      change ((q.shape.enter e).arrive (step x n)).pair w = _; rw [Axis.pull]; change (q.shape.enter e).pair (w 0,fun i:Fin n => w i.succ) = _
      rw [Axis.enter_pair,q.who]
    put w v := by
      obtain ⟨⟨m,u⟩,rfl⟩ := join.surjective w
      obtain ⟨a,b⟩ := v
      rw [← editT,← editT]
      apply (step x n).cast.injective
      change (step x n).cast (((q.shape.enter e).arrive (step x n)).bridge (join (m,u)) (a,b)) = _
      rw [Axis.endorse]
      change (q.shape.enter e).bridge (join.symm (join (m,u))) (a,b) = join.symm (join (m,_))
      simp only [Equiv.symm_apply_apply,Axis.enter_bridge,q.put] }
def pickTwo (d : Tape) (e : Seal x d) :
    {n : ℕ} → (i j : Fin n) → i<j → Double x d n i j
| 0,i,_,_ => i.elim0
| n+1,i,j,h => Fin.cases (motive:=fun j => i<j → Double x d (n+1) i j)
   (fun h => False.elim (Nat.not_lt_zero _ h)) (fun l => Fin.cases (motive:=fun i => i<l.succ → Double x d (n+1) i l.succ)
    (fun _ => firstTwo x d l (pick x d e l)) (fun k t =>
      laterTwo x d e k l (pickTwo d e k l ((Fin.succ_lt_succ_iff).mp t))) i) j h
end Loom

end IntegerMultiplication
end Computability
end OAI
