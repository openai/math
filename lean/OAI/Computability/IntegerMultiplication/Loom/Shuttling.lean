import OAI.Computability.IntegerMultiplication.Loom.Thread
import OAI.Computability.IntegerMultiplication.Port.Lag

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims Port
variable {J T : Type} [DecidableEq J] {n : ℕ} (f : J ≃ Fin n) (t : Series T)
variable (P G B : Tape)
abbrev Keys (P G B : Tape) (J T : Type) :=
  Pin P × (J→T) × Pin G × (J→T) × Pin B
abbrev arrays := Path P (threads t f) G (threads t f) B

variable {P G B} in
def ask (x : Keys P G B J T) (s : Spot J) : T :=
  if s.1 then x.2.2.2.1 s.2 else x.2.1 s.2
variable {P G B} in
def give (x : Keys P G B J T) (s : Spot J) (v : T) : Keys P G B J T :=
  if s.1 then (x.1,x.2.1,x.2.2.1,Function.update x.2.2.2.1 s.2 v,x.2.2.2.2) else
    (x.1,Function.update x.2.1 s.2 v,x.2.2.1,x.2.2.2.1,x.2.2.2.2)
variable {P G B} in
@[simp] theorem got (x : Keys P G B J T) (s i : Spot J) (v : T) :
    ask (give x s v) i = if i=s then v else ask x i := by
  rcases s with ⟨_ | _, s⟩; all_goals rcases i with ⟨_ | _,i⟩
  all_goals by_cases e : i=s <;> simp [give, ask, e]

def ranking (i : J) := (f i).val
omit [DecidableEq J] in
theorem well : Function.Injective (ranking f) := fun _ _ h => f.injective (Fin.ext h)
omit [DecidableEq J] in
theorem edge (i : J) : ranking f i<n := (f i).isLt
abbrev leftF (d : Tape) (i : J) := Rack d (ranking f i)
abbrev rightF (d : Tape) (i : J) := Rack d (n-ranking f i-1)
abbrev midF (d : Tape) (i j : J) := Rack d (ranking f j-ranking f i-1)

variable (d : Tape)
def preamble (s : Spot J) : Tape :=
  P ++ if s.1 then Rack d n ++ (G ++ leftF f d s.2)
       else leftF f d s.2
def appendix (s : Spot J) : Tape :=
  if s.1 then rightF f d s.2 ++ B
  else rightF f d s.2 ++ (G ++ (Rack d n ++ B))
-- parenthesization match Slot.exit applied once q on G×D×B via Seal. use rw append_assoc for discrepancy
def silence (s q : Spot J) : Tape :=
  if s.1=q.1 then midF f d s.2 q.2 else
    rightF f d s.2 ++ (G ++ leftF f d q.2)

omit [DecidableEq J] in
@[simp] theorem preamble_false (i : J) : preamble f P G d (false,i) = P ++ leftF f d i := rfl
omit [DecidableEq J] in
@[simp] theorem preamble_true (i : J) : preamble f P G d (true,i) = P ++ (Rack d n ++ (G ++ leftF f d i)) := rfl
omit [DecidableEq J] in
@[simp] theorem appendix_false (i : J) : appendix f G B d (false,i) = rightF f d i ++ (G ++ (Rack d n ++ B)) := rfl
omit [DecidableEq J] in
@[simp] theorem appendix_true (i : J) : appendix f G B d (true,i) = rightF f d i ++ B := rfl
omit [DecidableEq J] in
@[simp] theorem silence_false_false (i j : J) : silence f G d (false,i) (false,j) = midF f d i j := rfl
omit [DecidableEq J] in
@[simp] theorem silence_false_true (i j : J) : silence f G d (false,i) (true,j) = rightF f d i ++ (G ++ leftF f d j) := rfl
omit [DecidableEq J] in
@[simp] theorem silence_true_true (i j : J) : silence f G d (true,i) (true,j) = midF f d i j := rfl
private def couple {S R : Tape} {A C : Type} {a : Series A} {c : Series C}
    (h : Seal a S) (g : Seal c R) :
    Seal (a.cart c) (S++R) := (h.split g).thenDo (unite S R)

theorem atSlot (h : Seal t d) (s : Spot J) :
    ∃ v : Slot (arrays f t P G B) (preamble f P G d s) t (appendix f G B d s),
      ∀ x w,v.read x=ask x s ∧ v.alter x w=give x s w := by
  cases s with
  | mk wing i =>
    obtain ⟨q,u⟩ := monoRay t f h i
    cases wing
    · simp only [preamble_false,appendix_false,leftF,rightF,ranking,arrays,Path,Board]
      let full := couple (Adopt.same (layout G)) (couple (undye t f h) (Adopt.same (layout B)))
      refine ⟨(q.exit full).enter (Adopt.same (layout P)),?_⟩
      rintro ⟨p,m,g,l,b⟩ w
      simp only [Slot.enter_read,Slot.exit_read,Slot.enter_alter,Slot.exit_alter]
      simp [ask,give,(u m w).1,(u m w).2]
    simp only [preamble_true,appendix_true,leftF,rightF,ranking,arrays,Path,Board]
    refine ⟨(((q.exit (Adopt.same (layout B))).enter (Adopt.same (layout G))).enter
      (undye t f h)).enter (Adopt.same (layout P)),?_⟩
    rintro ⟨p,m,g,l,b⟩ w
    simp only [Slot.enter_read,Slot.exit_read,Slot.enter_alter,Slot.exit_alter]
    simp [ask,give,(u l w).1,(u l w).2]

theorem crossing (h : Seal t d) (s q : Spot J) (g : Lag.early (ranking f) s q) :
    ∃ v : Axis (arrays f t P G B) (preamble f P G d s) t (silence f G d s q) t
        (appendix f G B d q),
      ∀ x a b,v.pair x=(ask x s,ask x q) ∧ v.bridge x (a,b)=give (give x s a) q b := by
  cases s with
  | mk i x =>
    cases q with
    | mk j y =>
      cases i <;> cases j
      · obtain ⟨v,u⟩ := doubleRay t f h x y (show (f x).val<(f y).val from
          (g.elim (fun h => Bool.noConfusion h.2) (fun h => h.2)))
        simp only [preamble_false,appendix_false,silence_false_false,leftF,rightF,ranking,midF,arrays,Path,Board]
        let full := couple (Adopt.same (layout G)) (couple (undye t f h) (Adopt.same (layout B)))
        refine ⟨(v.exit full).enter (Adopt.same (layout P)),?_⟩
        rintro ⟨p,m,z,l,b⟩ c k
        simp only [Axis.enter_pair,Axis.enter_bridge,Axis.exit_pair,Axis.exit_bridge]
        simp [ask,give,(u m (c,k)).1,(u m (c,k)).2]
      · obtain ⟨a,u⟩ := monoRay t f h x
        obtain ⟨w,i⟩ := monoRay t f h y
        simp only [preamble_false,appendix_true,silence_false_true,leftF,rightF,ranking,arrays,Path,Board]
        refine ⟨(Axis.both a ((w.exit (Adopt.same (layout B))).enter (Adopt.same (layout G)))).enter
          (Adopt.same (layout P)),?_⟩
        rintro ⟨p,m,z,l,b⟩ c k
        simp only [Axis.enter_pair,Axis.enter_bridge,Axis.both_bridge,Axis.both_pair,
          Slot.enter_read,Slot.enter_alter,Slot.exit_read,Slot.exit_alter,(u m c).2,(u m c).1,(i l k).2,(i l k).1]
        simp [ask,give]
      · simp [Lag.early] at g
      obtain ⟨v,u⟩ := doubleRay t f h x y (show (f x).val<(f y).val from
        g.elim (fun h => Bool.noConfusion h.1) (fun h => h.2))
      simp only [preamble_true,appendix_true,silence_true_true,leftF,rightF,ranking,midF,arrays,Path,Board]
      refine ⟨(((v.exit (Adopt.same (layout B))).enter (Adopt.same (layout G))).enter
        (undye t f h)).enter (Adopt.same (layout P)),?_⟩
      rintro ⟨p,m,z,l,b⟩ c k
      simp only [Axis.enter_pair,Axis.enter_bridge,Axis.exit_pair,Axis.exit_bridge,(u l (c,k)).1,(u l (c,k)).2]
      simp [ask,give]

omit [DecidableEq J] in
theorem length_slot (s : Spot J) :
    (preamble f P G d s).length + (appendix f G B d s).length + d.length =
    P.length+G.length+B.length+2*d.length*n := by
  obtain ⟨_ | _,i⟩ := s
  all_goals
    simp only [appendix,preamble,Bool.false_eq_true,ite_false,ite_true,leftF,rightF,List.length_append,pieces]
    have e := edge f i
    have v : ranking f i + (n-ranking f i-1)+1=n := by omega
    have := congrArg (d.length * ·) v
    simp only [Nat.mul_add,Nat.mul_one] at this
    grind -- one goal maybe works

omit [DecidableEq J] in
theorem length_cross (s q : Spot J) (g : Lag.early (ranking f) s q) :
    (preamble f P G d s).length + (silence f G d s q).length + (appendix f G B d q).length +
        2*d.length = P.length+G.length+B.length+2*d.length*n := by
  rcases s with ⟨_ | _,i⟩ <;> rcases q with ⟨_ | _,j⟩
  all_goals
    simp only [appendix,preamble,silence,Bool.true_eq_false,Bool.false_eq_true,ite_false,ite_true,
      leftF, midF,rightF,List.length_append,pieces]
    have a := edge f i; have b := edge f j
    simp [Lag.early] at g
  · have v : ranking f i+(ranking f j-ranking f i-1)+(n-ranking f j-1)+2=n := by omega
    have := congrArg (d.length * ·) v
    simp only [Nat.mul_add] at this
    grind
  · have v : ranking f i+(n-ranking f i-1)+ranking f j+(n-ranking f j-1)+2=2*n := by omega
    have := congrArg (d.length * ·) v
    simp only [Nat.mul_add] at this
    grind
  · have v : ranking f i+(ranking f j-ranking f i-1)+(n-ranking f j-1)+2=n := by omega
    have := congrArg (d.length * ·) v
    simp only [Nat.mul_add] at this
    grind
end Loom

end IntegerMultiplication
end Computability
end OAI
