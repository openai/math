import OAI.Computability.NearSquareRoot.CommonTapes

/-! # Effective routing for the literal input and output adapters

Each route has an executable partial inverse. An operation on a tape outside
the route writes back its current symbol and leaves its head still.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Pipeline
open IntegerMultiplication TM

structure Route (I J : Type) where
  index : I ↪ J
  localIndex : J → Option I
  exactIndex : ∀ i j, localIndex j = some i ↔ index i = j

namespace Route
variable {A Q I J D : Type} (r : Route I J)

def put (localData : I → D) (other : J → D) (j : J) : D :=
  ((r.localIndex j).map localData).getD (other j)

theorem put_eq (localData : I → D) (other : J → D) :
    r.put localData other = CommonTapes.extend r.index localData other := by
  funext j
  cases h : r.localIndex j with
  | none =>
    rw [CommonTapes.extend_off]
    · simp [put,h]
    · rintro ⟨i,hi⟩
      have := (r.exactIndex i j).mpr hi
      simp [h] at this
  | some i =>
    obtain rfl := (r.exactIndex i j).mp h
    simp [put,h]

def rule (m : Rule A Q I) : Rule A Q J := fun q read =>
  (m q (read ∘ r.index)).map (fun (q',op) => (q',r.put op (fun j => (read j,.stay))))

theorem rule_eq (m : Rule A Q I) : r.rule m = CommonTapes.rule r.index m := by
  funext q read
  simp [rule,CommonTapes.rule,put_eq]

theorem lift (m : Rule A Q I) (other : J → Tape A)
    {q q' : Q} {s u : I → Tape A} {n cells : ℕ}
    (run : Trace (advance m) ⟨q,s⟩ n ⟨q',u⟩) (halt : advance m ⟨q',u⟩ = none)
    [Fintype J] (space : VisitsAtMost m ⟨q,s⟩ n cells) :
    Trace (advance (r.rule m)) ⟨q,r.put s other⟩ n ⟨q',r.put u other⟩ ∧
      advance (r.rule m) ⟨q',r.put u other⟩ = none ∧
      VisitsAtMost (r.rule m) ⟨q,r.put s other⟩ n (cells + Fintype.card J) := by
  rw [rule_eq,put_eq,put_eq]
  exact ⟨CommonTapes.trace _ _ _ run, (CommonTapes.advance_config _ _ _ _).trans
    (by rw [halt]), CommonTapes.visits _ _ _ _ _ _ space⟩

end Route

abbrev Index (I : Type) := Bool ⊕ I

/-- Two dedicated literal tapes flank the original machine's tape bank. -/
def store {I D : Type} (input output : D) (core : I → D) : Index I → D
  | .inl false => input
  | .inl true => output
  | .inr i => core i

variable {I : Type} [DecidableEq I]

def inputRoute (inp : I) : Route Bool (Index I) where
  index := ⟨fun b => if b then .inr inp else .inl false, by intro a b h; cases a <;> cases b <;> simp_all⟩
  localIndex
    | .inl false => some false
    | .inr j => if j = inp then some true else none
    | _ => none
  exactIndex := by
    intro b j
    change _ ↔ (if b then Sum.inr inp else Sum.inl false) = j
    cases b <;> rcases j with (b | i)
    all_goals first | cases b <;> simp | by_cases he : i = inp <;> (simp [he] <;> solve_by_elim [Ne.symm])

def outputRoute (out : I) : Route Bool (Index I) where
  index := ⟨fun b => if b then .inl true else .inr out, by intro a b h; cases a <;> cases b <;> simp_all⟩
  localIndex
    | .inl true => some true
    | .inr j => if j = out then some false else none
    | _ => none
  exactIndex := by
    intro b j
    change _ ↔ (if b then Sum.inl true else Sum.inr out) = j
    cases b <;> rcases j with (b | i)
    all_goals first | cases b <;> simp | by_cases he : i = out <;> (simp [he] <;> solve_by_elim [Ne.symm])

def coreRoute (I : Type) : Route I (Index I) where
  index := Function.Embedding.inr
  localIndex := Sum.elim (fun _ => none) some
  exactIndex := by intro i j; cases j <;> simp [eq_comm]

omit [DecidableEq I] in
theorem core_store {D : Type} (input output : D) (s t : I → D) :
    (coreRoute I).put t (store input output s) = store input output t := by
  funext j
  rcases j with (b | i)
  · cases b <;> rfl
  · rfl

end CommonAlphabet.Pipeline

end NearSquareRoot
end Computability
end OAI
