import OAI.Computability.IntegerMultiplication.Loom.Arrivals
import OAI.Computability.IntegerMultiplication.Port.Lag

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims Port Adic
variable {p : ℕ} {J T : Type} [DecidableEq J] {j : ℕ} [NeZero p]
variable {n : ℕ} (f : J ≃ Fin n)
variable {P G B : Tape}
omit [DecidableEq J] in
private theorem beforeNe (i s : Spot J) (e : Lag.early (ranking f) i s) :
    i≠s := by rintro rfl; simp [Lag.early] at e

-- action of Equiv on spectators ignores, numbers as prescribed
structure Delivers {A C : Type} (u : A → A) (d : C → C) (v : A → C) : Prop where
  acts x : v (u x) = d (v x)

noncomputable section
abbrev fieldSlot (s : Spot J) {p j : ℕ} {P G B : Tape} :=
  Slot (arrays f (line p j) P G B) (preamble f P G (field p j) s) (line p j)
    (appendix f G B (field p j) s)
abbrev fieldAxis (s q : Spot J) {p j : ℕ} {P G B : Tape} :=
  Axis (arrays f (line p j) P G B) (preamble f P G (field p j) s) (line p j)
    (silence f G (field p j) s q) (line p j) (appendix f G B (field p j) q)

def oneStop (s : Spot J) {p j P G B} : fieldSlot f s (p:=p) (j:=j) (P:=P) (G:=G) (B:=B) :=
  Classical.choose (atSlot f _ _ _ _ _ (Adopt.same _) s)
theorem one_use (s : Spot J) {p j} (x : Keys P G B J (Block p j)) (v) :
    (oneStop f s).read x=ask x s ∧ (oneStop f s).alter x v=give x s v :=
  Classical.choose_spec (atSlot f _ _ _ _ _ (Adopt.same _) s) x v

def twoStops (s q : Spot J) (h : Lag.early (ranking f) s q) {p j P G B} :
    fieldAxis f s q (p:=p) (j:=j) (P:=P) (G:=G) (B:=B) :=
  Classical.choose (crossing f _ _ _ _ _ (Adopt.same _) s q h)
theorem two_use (s q : Spot J) (h : Lag.early (ranking f) s q) {p j}
    (x : Keys P G B J (Block p j)) (a b) :
    (twoStops f s q h).pair x=(ask x s,ask x q) ∧ (twoStops f s q h).bridge x (a,b) =
      give (give x s a) q b :=
  Classical.choose_spec (crossing f _ _ _ _ _ (Adopt.same _) s q h) x a b

private def grab (c : Pinpoint p) (j : ℕ) :=
  slideOver (fun x => glide (c.stamp j * index p j x))

def reflect (r : Lag J p) (e : r.legal (ranking f))
    (P G B : Tape) (j : ℕ) : Keys P G B J (Block p j) ≃ Keys P G B J (Block p j) :=
  match r with
  | .width i a => (oneStop f i).tune (sweep a j)
  | .gather i k b => (twoStops f k i e).tune (grab b j)
  | .pivot i k => (twoStops f (false,i) (true,k) (Or.inl ⟨rfl,rfl⟩)).tune (Equiv.prodComm _ _)

def watcher {p j : ℕ} (x : Keys P G B J (Block p j)) :=
  (x.1,x.2.2.1,x.2.2.2.2)
abbrev fieldId {p j : ℕ} (x : Keys P G B J (Block p j)) : Duplex J (Block p j) :=
  (x.2.1,x.2.2.2.1)
def chase (x : Keys P G B J (Block p j)) : Duplex J (Tower p j) :=
  ((index p j) ∘ x.2.1,(index p j) ∘ x.2.2.2.1)
-- structural
omit [DecidableEq J] in
theorem broadcast {p j : ℕ} {x y : Keys P G B J (Block p j)} (d : watcher x=watcher y)
    (h : ∀ i,ask x i = ask y i) : x=y := by
  cases x with
  | mk a x =>
    cases x with
    | mk b x =>
      cases x with
      | mk c x =>
        cases x with
        | mk z u =>
          rcases y with ⟨a',b',c',z',u'⟩
          cases d
          -- dependent cases d error?
          have eb : b=b' := funext fun i => h (false,i)
          have ez : z=z' := funext fun i => h (true,i)
          rw [eb,ez]

include f in
-- number of labels?
theorem walk (r : Lag J p) (e : Lag.legal (ranking f) r)
    (x : Keys P G B J (Block p j)) :
    watcher (reflect f r e _ _ _ j x) = watcher x ∧
    chase (reflect f r e _ _ _ j x) = Lag.fire j (chase x) r := by
  have same (x : Keys P G B J (Block p j)) (a : Spot J) v :
      watcher (give x a v)=watcher x := by unfold give; split <;> rfl
  have listen (x : Keys P G B J (Block p j)) (s : Spot J) :
      hear (chase x) s=index p j (ask x s) := by obtain ⟨_ | _,i⟩ := s <;> rfl
  cases r with
  | width i a =>
    change watcher ((oneStop f i).alter x _) = _ ∧ chase ((oneStop f i).alter x _) = _
    rw [(one_use f i x (ask x i)).1,(one_use f i x _).2, Lag.fire, same]
    refine ⟨rfl,hear_all (fun k => ?_)⟩
    rw [listen, listen, Port.placed, got]
    split
    next eq => subst k; rw [Adic.inj]
    next eq => rw [listen]
  | gather i k b =>
    have ok : Lag.early (ranking f) k i := e
    change watcher ((twoStops f k i e).bridge x _) = _ ∧ chase ((twoStops f k i e).bridge x _) = _
    have d := two_use f k i ok x (ask x k) (grab b j (ask x k,ask x i)).2
    simp only [d.1,grab,slideOver,Equiv.coe_fn_mk] -- simplify pair; maybe no d.2 due DSL
    rw [ (two_use f k i ok x _ _).2,Lag.fire,same,same]
    refine ⟨rfl,hear_all (fun m => ?_)⟩
    rw [listen,listen (x:=x), Port.placed,got]
    by_cases g : m=i
    · subst m
      simp only [ite_true, listen, Adic.move_nat]
    rw [got]
    by_cases hk : m=k
    · subst m
      simp [listen,g]
    simp [g,hk,listen]
  | pivot i k =>
    let a : Spot J := (false,i)
    let b : Spot J := (true,k)
    have d := two_use f a b (Or.inl ⟨rfl,rfl⟩) x (ask x b) (ask x a)
    change watcher ((twoStops f a b _).bridge x _) = _ ∧ chase ((twoStops f a b _).bridge x _) = _
    simp only [show Axis.pair (twoStops f (false,i) (true,k) _) x = _ from d.1, Equiv.prodComm_apply]
    change watcher ((twoStops f a b _).bridge x (ask x b,ask x a)) = _ ∧
      chase ((twoStops f a b _).bridge x (ask x b,ask x a)) = place (place (chase x) a _) b _
    rw [d.2, same,same]
    refine ⟨rfl,hear_all (fun m => ?_)⟩
    rw [listen,placed,placed,got,got,listen (x:=x)]
    simp_rw [listen]
    by_cases g : m=b <;> by_cases d : m=a <;> simp [g,d] <;> rfl
end
end Loom

end IntegerMultiplication
end Computability
end OAI
