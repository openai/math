import OAI.Computability.NearSquareRoot.ScheduleGeneratorFunction
import Batteries.Tactic.OpenPrivate

/-! # Computable ranks for every state of the fixed-width alphabet simulator -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Numbering
open private phases from OAI.Computability.NearSquareRoot.CommonAlphabetNumbering
abbrev splitPhase := @phases
end CommonAlphabet.Numbering

namespace Generator
open CommonAlphabet IntegerMultiplication

namespace Phase

abbrev Actions := List (ℕ × ℕ)
abbrev State := (ℕ × List ℕ) ⊕ (ℕ × Actions × ℕ × ℕ) ⊕
  (ℕ × List (List ℕ) × ℕ) ⊕ (ℕ × List ℕ × ℕ)

abbrev ready (q : ℕ) (a : List ℕ) : State := .inl (q,a)
abbrev work (q : ℕ) (o : Actions) (m j : ℕ) : State := .inr (.inl (q,o,m,j))
abbrev read (q : ℕ) (b : List (List ℕ)) (j : ℕ) : State := .inr (.inr (.inl (q,b,j)))
abbrev rewind (q : ℕ) (a : List ℕ) (j : ℕ) : State := .inr (.inr (.inr (q,a,j)))

variable {A Q : ℕ → Type} {I : Type}
variable (a : ∀ x, Numbering (A x)) (q : ∀ x, Numbering (Q x)) (i : Numbering I)
variable (w : ℕ → ℕ) (ha : Computable fun x => (a x).size)
  (hq : Computable fun x => (q x).size) (hw : Computable w)

def actions : Presentation (fun x => i.arrow ((a x).prod Numbering.move)) Actions :=
  Presentation.arrow (Computable.const i.size)
    ((Presentation.scalar a ha).prod (Presentation.scalar (fun _ => Numbering.move) (Computable.const 3)))

def cached : Presentation (fun x => i.arrow (a x)) (List ℕ) :=
  Presentation.arrow (Computable.const i.size) (Presentation.scalar a ha)

def ternaryActions : Presentation (fun _ => i.arrow (Numbering.ternary.prod Numbering.move)) Actions :=
  actions (fun _ => Numbering.ternary) i (Computable.const 3)

/-- One four-way sum suffices independently of every alphabet and state cardinality. -/
def states : Presentation (fun x => Numbering.controller (a x) (q x) i (w x)) State := by
  let pc := Presentation.scalar q hq
  let cache := cached a i ha
  let op := actions a i ha
  let pos := Presentation.scalar (fun x => Numbering.fin (w x)) hw
  let mode := Presentation.scalar (fun _ => Numbering.mode) (Computable.const 3)
  let trit := Presentation.scalar (fun _ => Numbering.ternary) (Computable.const 3)
  let buf := Presentation.arrow (Computable.const i.size)
    (Presentation.arrow (N := fun x => Numbering.fin (w x)) hw trit)
  let body := (pc.prod cache).sum ((pc.prod (op.prod (mode.prod pos))).sum
    ((pc.prod (buf.prod pos)).sum (pc.prod (cache.prod pos))))
  exact ⟨fun x v => body.view x (Numbering.splitPhase (w x) v), body.size_eff,body.encode,
    body.encode_eff,body.decode,body.decode_eff,
    fun x v => body.encode_view x (Numbering.splitPhase (w x) v),
    fun x v => body.decode_rank x (Numbering.splitPhase (w x) v)⟩

def view (x : ℕ) : PC (A x) (Q x) I (w x) → State
  | .ready z c => ready ((q x).equiv z).val (i.all.map (fun l => ((a x).equiv (c l)).val))
  | .work z op mode j => work ((q x).equiv z).val (i.all.map (fun l =>
      (((a x).equiv (op l).1).val,(Numbering.move.equiv (op l).2).val))) (Numbering.mode.equiv mode).val j.val
  | .readBlock z b j => read ((q x).equiv z).val (i.all.map fun l =>
      (List.finRange (w x)).map fun k => (Numbering.ternary.equiv (b l k)).val) j.val
  | .rewind z c j => rewind ((q x).equiv z).val (i.all.map (fun l => ((a x).equiv (c l)).val)) j.val

theorem states_view (x : ℕ) (v : PC (A x) (Q x) I (w x)) :
    (states a q i w (ha := ha) (hq := hq) (hw := hw)).view x v = view a q i w x v := by
  cases v with
  | ready => rfl
  | work => rfl
  | rewind => rfl
  | readBlock =>
    change read _ (i.all.map (fun l => ((List.finRange _).map id).map _)) _ = _
    simp [view,read,Presentation.scalar,Numbering.fin]
    rfl

def ranks (r : I → Option Bool) : List ℕ :=
  i.all.map (fun l => (Numbering.ternary.equiv (r l)).val)

def moves (op : I → Option Bool × TM.Move) : Actions :=
  i.all.map (fun l => ((Numbering.ternary.equiv (op l).1).val,(Numbering.move.equiv (op l).2).val))

def observe (x : ℕ) (step : Option (PC (A x) (Q x) I (w x) × (I → Option Bool × TM.Move))) :=
  step.map fun t => (view a q i w x t.1,moves i t.2)

end Phase
end Generator

end NearSquareRoot
end Computability
end OAI
