import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.PriceGame.States
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength

/-! Actual finite Boolean-stack procedures for a duplicated price row. Each procedure
comes with a kernel-checked polynomial running time and a clean input/output convention. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open Procedure

/-- The unary size witness is part of the source complexity bound. Each element in
the resulting row is encoded in ordinary binary. -/
noncomputable def addressRangeP : Procedure unaryCode (listCode Nat.bits) List.range := by
  let elem : Procedure (prodCode unaryCode emptyCode) Nat.bits (fun i : ℕ × Unit => i.1) :=
    unaryToBits.comp (first unaryCode emptyCode)
  let p := tabulate (f := fun (_ : Unit) (i : ℕ) => i) 0 elem
  let input := (identity unaryCode).pair (constant unaryCode emptyCode ())
  exact (p.comp input).congrFun (by intro n; simp [id_eq])

/-- Return a list's actual length in unary, so it can drive a tabulation. -/
noncomputable def rowSizeP {α : Type} (enc : α → List Bool) (d : α) :
    Procedure (listCode enc) unaryCode List.length := by
  let step := unarySuccessor.comp (second enc unaryCode)
  let rep := foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _ => n+1) n)).length ≤ _
    rw [fold_count]
    simp only [unaryCode, List.length_replicate, Polynomial.eval_X, List.length_take]
    have h := list_length_le_code enc xs
    omega)
  let start := (identity (listCode enc)).pair (constant (listCode enc) unaryCode 0)
  exact (rep.comp start).congrFun (by
    intro xs; simpa only [Function.comp_apply, id_eq, Nat.zero_add] using fold_count xs 0)

noncomputable def ratMinP : Procedure (prodCode ratCode ratCode) ratCode (fun z => min z.1 z.2) :=
  (conditional OracleSpec.Arithmetic.ratLe (first ratCode ratCode) (second ratCode ratCode)).congrFun
    (by rintro ⟨a,b⟩; simp [min_def])

noncomputable def ratMaxP : Procedure (prodCode ratCode ratCode) ratCode (fun z => max z.1 z.2) :=
  (conditional OracleSpec.Arithmetic.ratLe (second ratCode ratCode) (first ratCode ratCode)).congrFun
    (by rintro ⟨a,b⟩; simp [max_def])

noncomputable def medianP : Procedure (prodCode ratCode (prodCode ratCode ratCode)) ratCode
    (fun t => States.median₃ t.1 t.2.1 t.2.2) := by
  let a := first ratCode (prodCode ratCode ratCode)
  let bc := second ratCode (prodCode ratCode ratCode)
  let b := (first ratCode ratCode).comp bc
  let c := (second ratCode ratCode).comp bc
  let lo := ratMinP.comp (a.pair b)
  let hi := ratMaxP.comp (a.pair b)
  exact (ratMaxP.comp (lo.pair (ratMinP.comp (hi.pair c)))).congrFun (by intro t; rfl)

noncomputable def natEqP : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun z => decide (z.1 = z.2)) := by
  let flip := binaryLt.comp (swap Nat.bits Nat.bits)
  exact (conditional binaryLt (constant _ boolCode false) (boolNot.comp flip)).congrFun (by
    rintro ⟨a,b⟩
    change (if decide (a < b) then false else !decide (b < a)) = decide (a = b)
    rcases lt_trichotomy a b with h | h | h <;> simp_all <;> omega)

abbrev LiftContext := ℕ × (List ℚ × List ℚ)
def liftCode : LiftContext → List Bool := prodCode Nat.bits (prodCode (listCode ratCode) (listCode ratCode))

/-- Single parent coordinate in an override. The first field is the designated child address.
The two finite arrays contain the parent's baseline and the child's prices respectively. -/
def liftCell (c : LiftContext) (i : ℕ) : ℚ :=
  let get (xs : List ℚ) (j : ℕ) := (xs.drop j).headD 0
  if i = c.1 / 2 then get c.2.2 c.1
  else States.median₃ (get c.2.1 i) (get c.2.2 (2*i)) (get c.2.2 (2*i+1))

noncomputable def liftCellP : Procedure (prodCode unaryCode liftCode) ratCode
    (fun v => liftCell v.2 v.1) := by
  let data := prodCode unaryCode liftCode
  let i := unaryToBits.comp (first unaryCode liftCode)
  let ctx := second unaryCode liftCode
  let erow := listCode ratCode
  let q := (first Nat.bits (prodCode erow erow)).comp ctx
  let rows := (second Nat.bits (prodCode erow erow)).comp ctx
  let base := (first erow erow).comp rows
  let child := (second erow erow).comp rows
  let parent := binaryDiv.comp (q.pair (constant data Nat.bits 2))
  let same := natEqP.comp (i.pair parent)
  let atQ := (listGet ratCode 0).comp (q.pair child)
  let atI := (listGet ratCode 0).comp (i.pair base)
  let atL := (listGet ratCode 0).comp ((double.comp i).pair child)
  let atR := (listGet ratCode 0).comp ((doubleOne.comp i).pair child)
  exact (conditional same atQ (medianP.comp (atI.pair (atL.pair atR)))).congrFun
    (by intro v; simp only [Function.comp_apply, id_eq, decide_eq_true_eq, liftCell])

def liftRow (c : LiftContext) : List ℚ := (List.range c.2.1.length).map (liftCell c)

noncomputable def liftRowP : Procedure liftCode (listCode ratCode) liftRow := by
  let erow := listCode ratCode
  let rows := second Nat.bits (prodCode erow erow)
  let base := (first erow erow).comp rows
  let count := (rowSizeP ratCode 0).comp base
  exact ((tabulate (f:=liftCell) 0 liftCellP).comp (count.pair (identity liftCode))).congrFun
    (by intro v; rfl)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
