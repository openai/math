import OAI.Computability.NearSquareRoot.SynchronizedLayers
import OAI.Computability.NearSquareRoot.SynchronizedAxisWord
import OAI.Computability.NearSquareRoot.PhaseProgramRelease

/-! # A fixed-tape generator for synchronized slot descriptors

The output explicitly records one optional instruction per physical address block.
Each round emits its permutation, diagonal, and selected-bit Walsh instruction rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedLayers.ScheduleProgram

open IntegerMultiplication IntegerMultiplication.Code

variable {X : Type}

def kindCode : Kind → Bool × Bool
  | .permutation => (false, false)
  | .diagonal => (false, true)
  | .walsh => (true, false)

def mask (kind : X → Kind) (s : Kind) (x : X) : Option X :=
  if kind x = s then some x else none

abbrev Row (X : Type) := (Bool × Bool) × List (Option X)

def row (kind : X → Kind) (s : Kind) (p : List (List X) × Tally) : Row X :=
  (kindCode s, p.1.map (fun w => ((w.map (mask kind s)).drop p.2.length).headD none))

def cycle (kind : X → Kind) (p : List (List X) × Tally) : List (Row X) :=
  [row kind .permutation p, row kind .diagonal p, row kind .walsh p]

def plan (kind : X → Kind) (p : List (List X) × Tally) : List (Row X) :=
  (Iter.lineup p.2).flatMap (fun t => cycle kind (p.1, t))

variable [Codec X] {kind : X → Kind}

private theorem mask_poly (h : ∀ s, Poly (fun x => decide (kind x = s))) (s : Kind) :
    Poly (mask kind s) := by
  have hm := Code.Poly.choose (h s) (Easy.some (X := X)).poly (Code.Poly.const (none : Option X))
  change Poly (fun x => if kind x = s then some x else none)
  simpa only [Bool.cond_decide] using hm

private theorem row_poly (h : ∀ s, Poly (fun x => decide (kind x = s))) (s : Kind) :
    Poly (row kind s) := by
  let fetch (p : Tally × List X) := Iter.pick none (p.2.map (mask kind s), p.1)
  have hm : Poly fetch :=
    ((Easy.snd.poly.compose (Poly.maps _ (mask_poly h s))).pair Easy.fst.poly).compose
      (Iter.facile _).poly
  exact (Code.Poly.const (kindCode s)).pair
    (Easy.exchange.poly.compose (Poly.push ([] : Tally) ([] : List X) hm))

private theorem cycle_poly (h : ∀ s, Poly (fun x => decide (kind x = s))) :
    Poly (cycle kind) := by
  exact ((row_poly h .permutation).pair
    (((row_poly h .diagonal).pair (((row_poly h .walsh).pair (Code.Poly.const [])).compose
      Code.Poly.cons)).compose Code.Poly.cons)).compose Code.Poly.cons

/-- One bounded stack program constructs the encoded global word for every set of inputs. -/
theorem plan_poly (h : ∀ s, Poly (fun x => decide (kind x = s))) : Poly (plan kind) := by
  have h₁ := (Easy.fst (X := List (List X)) (Y := Tally)).poly.pair
    (Easy.snd.poly.compose Iter.poly_line)
  exact (h₁.compose (Poly.push ([] : List (List X)) ([] : Tally) (cycle_poly h))).compose Easy.flatten.poly

/-- Actual time and the number of tape cells visited are polynomial in the encoded input. -/
theorem plan_machine (h : ∀ s, Poly (fun x => decide (kind x = s))) :
    PolyTreeMachine size send (fun p => send (plan kind p)) :=
  polyTreeMachine_of_BT ((plan_poly h).on (Dom.base _)) (Dom.base _)

open ShortFourier.AxisWord

/-- Classifier for the physically lowered short-axis instructions.
Tags 0 and 18 route addresses. Tags 10 and 14 apply Walsh.
The fixed-bit word replaces internal Walsh 14 with the route/10/route triple. -/
def instructionKind (x : Inst) : Kind :=
  if x.1.length = 0 ∨ x.1.length = 18 then .permutation
  else if x.1.length = 10 ∨ x.1.length = 14 then .walsh else .diagonal

private theorem test_tag (n : ℕ) : Poly (fun x : Inst => decide (x.1.length = n)) := by
  have h := ((Easy.fst (X := Tally) (Y := Tally × Bool)).poly.pair
    (Code.Poly.const (tally n))).compose (Iter.linked (X := Unit) (Y := Unit)).poly
  simpa using h

theorem instructionKind_poly (s : Kind) : Poly (fun x : Inst => decide (instructionKind x = s)) := by
  have H := Code.Poly.choose (test_tag 0) (Code.Poly.const (decide (Kind.permutation = s)))
    (Code.Poly.choose (test_tag 18) (Code.Poly.const (decide (Kind.permutation = s)))
      (Code.Poly.choose (test_tag 10) (Code.Poly.const (decide (Kind.walsh = s)))
        (Code.Poly.choose (test_tag 14) (Code.Poly.const (decide (Kind.walsh = s)))
          (Code.Poly.const (decide (Kind.diagonal = s))))))
  convert H using 1
  funext x
  by_cases hp : x.1.length = 0 <;> by_cases hr : x.1.length = 18 <;>
    by_cases h₁ : x.1.length = 10 <;> by_cases h₂ : x.1.length = 14 <;>
    simp [instructionKind, hp, hr, h₁, h₂]

theorem instruction_plan_machine :
    PolyTreeMachine size send (fun p => send (plan instructionKind p)) :=
  plan_machine instructionKind_poly

end SynchronizedLayers.ScheduleProgram

end NearSquareRoot
end Computability
end OAI
