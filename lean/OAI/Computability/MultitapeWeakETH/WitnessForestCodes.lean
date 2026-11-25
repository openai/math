import OAI.Computability.MultitapeWeakETH.WitnessWalkExact

/-! # Prefix codes and ordered emissions of a forest of private choices -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code
open private split_forest from OAI.Computability.MultitapeWeakETH.WitnessWalkExact

variable {D : Type} {visit : Visit D} {ctx : D}

/-- A derivation retains all local coefficient labels in visitation order. -/
def Accepts (visit : Visit D) (ctx : D) (js : List Job) (bits tail : Bits.Word) (labels : List Tally) :=
  ∃ n, Parses visit ctx js bits n tail labels

private theorem Parses.append {xs bits n mid a} (h : Parses visit ctx xs bits n mid a)
    {ys k tail b} (g : Parses visit ctx ys mid k tail b) :
    Parses visit ctx (xs++ys) bits (n+k) tail (a++b) := by
  induction h with
  | nil => simpa using g
  | cons call _ _ kids siblings =>
    simpa only [List.cons_append,List.append_assoc,Nat.add_assoc] using
      Parses.cons call (by assumption) (siblings g)

theorem accepts_append (xs ys : List Job) (bits tail : Bits.Word) (out : List Tally) :
    Accepts visit ctx (xs++ys) bits tail out ↔ ∃ mid a b,
      Accepts visit ctx xs bits mid a ∧ Accepts visit ctx ys mid tail b ∧ out = a++b := by
  constructor
  · rintro ⟨_,h⟩
    obtain ⟨n,k,mid,a,b,first,later,_,labels⟩ := split_forest h xs ys rfl
    exact ⟨mid,a,b,⟨n,first⟩,⟨k,later⟩,labels⟩
  · rintro ⟨_,_,_,⟨_,first⟩,⟨_,later⟩,rfl⟩
    exact ⟨_,first.append later⟩

theorem accepts_one (j : Job) (bits tail : Bits.Word) (out : List Tally) :
    Accepts visit ctx [j] bits tail out ↔ ∃ kids mid a b,
      visit ((ctx,j),bits) = some ((kids,mid),a) ∧ Accepts visit ctx kids mid tail b ∧ out = a++b := by
  constructor
  · rintro ⟨_,h⟩
    cases h with
    | cons call child siblings =>
      cases siblings
      exact ⟨_,_,_,_,call,⟨_,child⟩,by simp⟩
  · rintro ⟨_,_,_,_,call,⟨_,child⟩,rfl⟩
    exact ⟨_,by simpa using Parses.cons call child (Parses.nil tail)⟩

def Reads {X : Type} (visit : Visit D) (ctx : D) (jobs : List Job) (code : X → Bits.Word) (names : X → List Tally) :=
  ∀ bits tail labels, Accepts visit ctx jobs bits tail labels ↔ ∃ x, bits = code x ++ tail ∧ labels = names x

/-- Independent child codes concatenate in the stored site order, including
the empty placement fiber. The same dependent tuple determines every emission. -/
theorem reads_forest (n : ℕ) (X : Fin n → Type) (job : Fin n → Job)
    (code : ∀ i, X i → Bits.Word) (names : ∀ i, X i → List Tally)
    (each : ∀ i, Reads visit ctx [job i] (code i) (names i)) :
    Reads visit ctx (List.ofFn job)
      (fun x : ∀ i, X i => (List.ofFn (fun i => code i (x i))).flatten)
      (fun x : ∀ i, X i => (List.ofFn (fun i => names i (x i))).flatten) := by
  induction n with
  | zero =>
    intro bits tail labels
    simp only [List.ofFn_zero,List.flatten_nil,List.nil_append]
    constructor
    · rintro ⟨_,h⟩; cases h; exact ⟨fun i => i.elim0,rfl,rfl⟩
    · rintro ⟨_,rfl,rfl⟩; exact ⟨_,.nil _⟩
  | succ n ih =>
    let jobs := List.ofFn (fun i : Fin n => job i.succ)
    have rest := ih (fun i => X i.succ) (fun i => job i.succ) (fun i => code i.succ)
      (fun i => names i.succ) (fun i => each i.succ)
    intro bits tail labels
    rw [show List.ofFn job = [job 0] ++ jobs from List.ofFn_succ,accepts_append]
    constructor
    · rintro ⟨mid,a,b,head,body,rfl⟩
      obtain ⟨x,hx,rfl⟩ := (each 0 _ _ _).mp head
      obtain ⟨xs,rfl,rfl⟩ := (rest _ _ _).mp body
      refine ⟨Fin.cons x xs,?_,?_⟩
      · simpa only [List.ofFn_succ (n:=n),List.flatten_cons,Fin.cons_zero,Fin.cons_succ,List.append_assoc] using hx
      · simp only [List.ofFn_succ (n:=n),List.flatten_cons,Fin.cons_zero,Fin.cons_succ]
    · rintro ⟨x,rfl,rfl⟩
      let xs (i : Fin n) := x i.succ
      let mid := (List.ofFn fun i : Fin n => code i.succ (xs i)).flatten ++ tail
      let tags := (List.ofFn fun i : Fin n => names i.succ (xs i)).flatten
      refine ⟨mid,names 0 (x 0),tags,(each 0 _ _ _).mpr ⟨x 0,?_,rfl⟩,(rest _ _ _).mpr ⟨xs,rfl,rfl⟩,?_⟩
      · simp only [List.ofFn_succ (n:=n),List.flatten_cons,List.append_assoc]; rfl
      · simp only [List.ofFn_succ (n:=n),List.flatten_cons]; rfl

end OAI.Computability.MultitapeWeakETH.WitnessWalk
