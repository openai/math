import OAI.Computability.IntegerMultiplication.Code.Auto
import OAI.Computability.IntegerMultiplication.Code.Zip

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
variable {X Y Z S U : Type*} [Codec X] [Codec Y] [Codec Z] [Codec S]
variable [FiniteState X] [FiniteState S]

/-- Peel two tags x then y of arbitrary finite state types; do not pay for suffix. -/
private theorem peel_two (x : U → X) (s : U → S) (p q : U → Tree)
    (h : ∀ b a, Task (fun _ => 1)
        (fun i : {i : {i : U // x i = b} // s i.val = a} => p i.val.val)
        (fun i => q i.val.val)) :
    Task (fun _ => 1) (fun i => .fork (send (x i)) (.fork (send (s i)) (p i))) q :=
  Task.finite_select x fun b => Task.finite_select (fun i : {i : U // x i=b} => s i.val) (h b)

-- constant output fragment based on finite input, preserving growing suffix at unit cost
-- analogous to a Mealy transducer transition.
omit [Codec Y] in
theorem prepend_const (x : List Y) {pY : Y → Tree} (p : U → Tree) :
    -- `p` already the forest-encoded tail of a list (grammar same, even differing leaf codec)
    Task (fun _ => 0) p (fun i => x.foldr (fun y z => Tree.fork (pY y) z) (p i)) := by
  induction x with
  | nil => exact Task.self
  | cons x l ih =>
    exact (ih.compose (Task.supply (pY x) _)).conform (by simp) (by simp) (by simp)

def trans (step : X → S → S × List Y) (s : S × List Y) (x : X) : S × List Y :=
  let j := step x s.1
  (j.1,j.2.reverse ++ s.2)

/-- Any such transition prepending a fixed emission (here reversed, e.g. to push it on
a stack) has constant charge, because it only reads a fixed-size input and state. -/
private theorem transition (step : X → S → S × List Y) :
    Computes (fun _ => 1) (fun i : X × S × List Y => trans step i.2 i.1) := by
  apply peel_two (Prod.fst : X × S × List Y → X) (fun i => i.2.1) (fun i => send i.2.2) _
  intro b a
  let T := {i : {i : X × S × List Y // i.1=b} // i.val.2.1=a}
  have ee := prepend_const (pY := send) (step b a).2.reverse (fun i : T => send i.val.val.2.2)
  refine ((ee.compose (Task.supply (send (step b a).1) _)).mono (b' := fun _ => 1) (by simp)).conform (by simp) (by simp) (fun i => ?_)
  rcases i with ⟨⟨⟨j,z,l⟩,hj⟩,hz⟩
  dsimp at hj hz
  subst j z
  simp only [send_prod,trans]
  congr 1
  induction (step b a).2.reverse with
  | nil => rfl
  | cons y y' ih => simp [ih]

/-- Run a single finite-state transducer from left to right over a list of symbols,
producing arbitrary bounded emission words and the final state. Also returns the
output in forward order. -/
def machine (step : X → S → S × List Y) (input : List X × S) : List Y × S :=
  let r := input.1.foldl (trans step) (input.2,[])
  (r.2.reverse,r.1)

@[fun_prop]
theorem Easy.machine {step : X → S → S × List Y} {g : Z → List X × S} (h : Easy g) :
    Easy (fun i => machine step (g i)) := by
  open Classical in
  apply h.compose
  let R := fun i : List X × S × List Y => i.1.foldl (trans step) i.2
  have e : Easy R := by
    have hu := Task.foldLeft (X:=X) (Z:= S × List Y) (Y:=Unit)
      (fun _ => send) (fun _ => send) (fun _ => trans step) (fun _ _ => 1)
      (D := fun _ _ => True)
      ((transition step).on (fun i : {u : X × (S × List Y) × Unit // True} => (i.val.1,i.val.2.1)))
    refine Easy.of_bound (f := R) (a := fun i : List X × S × List Y => i.1.length+size i.1)
      -- actual arg label a
      ?_ 2 ?_
    · refine (hu.on (fun i => ⟨(i.1,i.2,()),by simp⟩)).conform ?_ ?_ (by simp [R])
      · intro x
        have hh (l : List X) : costSum (fun _ => 1) l = l.length := by induction l <;> simp_all [Nat.add_comm]
        dsimp only
        rw [Task.forest_send, size, hh]
      · intro; simp
    intro i
    simp only [size_prod]
    have := costSum_le_length_size i.1
    omega
  have v : Easy (fun i : List X × S => (i.1,i.2,([] : List Y))) := by fun_prop
  exact (v.compose e).compose (show Easy (fun i : S × List Y => (i.2.reverse,i.1)) from by fun_prop)

omit [Codec X] [Codec Y] [Codec S] [FiniteState X] [FiniteState S] in
/-- Useful extensional description. -/
theorem machine_nil (step : X → S → S × List Y) (s : S) :
    machine step ([],s)=([],s) := rfl

omit [Codec X] [Codec Y] [Codec S] [FiniteState X] [FiniteState S] in
theorem machine_acc (step : X → S → S × List Y) (l : List X) (s : S) (initial : List Y) :
    let (a,b) := machine step (l,s)
    l.foldl (trans step) (s,initial) = (b,a.reverse ++ initial) := by
  change l.foldl _ _ = ((machine step (l,s)).2,(machine step (l,s)).1.reverse++_)
  simp only [machine,List.reverse_reverse]
  induction l generalizing s initial with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons,trans]
    -- trans expanded?
    -- use transport of accumulator append
    change List.foldl (trans step) _ l = ((List.foldl (trans step) _ l).1, (List.foldl (trans step) _ l).2 ++ initial)
    rw [ih _ ((step x s).2.reverse++initial), ih _ ((step x s).2.reverse++[])]
    simp

omit [Codec X] [Codec Y] [Codec S] [FiniteState X] [FiniteState S] in
theorem machine_cons (step : X → S → S × List Y) (s : S) (x : X) (l : List X) :
    machine step (x::l,s) =
    let (a,output) := step x s
    let (out,b) := machine step (l,a)
    (output ++ out,b) := by
  obtain ⟨a,o,e⟩ : ∃ a o, step x s=(a,o) := ⟨_,_,rfl⟩
  obtain ⟨outs,b,h⟩ : ∃ outs b, machine step (l,a)=(outs,b) := ⟨_,_,rfl⟩
  have hh := machine_acc step l a o.reverse
  rw [h] at hh
  simp only at hh
  simp only [e,h]
  unfold machine
  simp only [List.foldl_cons,trans]
  change ( (List.foldl (trans step) ((step x s).1,(step x s).2.reverse ++ []) l).2.reverse, _)=_
  rw [e, List.append_nil, hh]
  simp

end Code

end IntegerMultiplication
end Computability
end OAI
