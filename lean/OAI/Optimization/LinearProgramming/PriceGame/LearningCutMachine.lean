import OAI.Optimization.LinearProgramming.PriceGame.LearningCutCode
import OAI.Optimization.LinearProgramming.PriceGame.LearningPathMachine

/-! Compile a tightened observation into literal binary-stack programs. Index tests, integer
minimum, and floor/ceiling of a rational input all execute on their serialized operands. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram

private noncomputable def natEqP {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Procedure.boolCode (fun x => decide (f x = g x)) := by
  apply (Procedure.boolAnd.comp
    ((Procedure.binaryLe.comp (p.pair q)).pair (Procedure.binaryLe.comp (q.pair p)))).congrFun
  intro x
  apply Bool.eq_iff_iff.mpr
  simp [le_antisymm_iff]

/-- Update one row and column, reading every old entry from the actual input matrix. -/
private noncomputable def tightenP {α : Type} (ea : α → List Bool) {n : ℕ}
    {d : α → Bounds n} {i j : α → Fin n} {c : α → ℤ}
    (dp : Procedure ea (matrixCode intCode n) d)
    (ip : Procedure ea Nat.bits (fun x => (i x).val))
    (jp : Procedure ea Nat.bits (fun x => (j x).val)) (cp : Procedure ea intCode c) :
    Procedure ea (matrixCode intCode n) (fun x => tightenArc (d x) (i x) (j x) (c x)) := by
  apply assembleMatrix
  intro a b
  let old := (readMatrix intCode 0 a b).comp dp
  let ra := natEqP (Procedure.constant ea Nat.bits a.val) ip
  let rb := natEqP (Procedure.constant ea Nat.bits b.val) jp
  let test := Procedure.boolAnd.comp (ra.pair rb)
  apply (Procedure.conditional test (minP.comp (old.pair cp)) old).congrFun
  intro x
  change (if (decide (a.val=(i x).val) && decide (b.val=(j x).val)) then
    min (d x a b) (c x) else d x a b) = _
  simp [tightenArc, Fin.ext_iff]

/-- Compile the three branches, including rejection of fractional equality. -/
noncomputable def cutMachine (n : ℕ) :
    Procedure (prodCode (cutObservationCode n) (matrixCode intCode n))
      (optionCode (matrixCode intCode n)) (fun x => addObservation x.2 x.1) := by
  let ea := prodCode (cutObservationCode n) (matrixCode intCode n)
  let eout := matrixCode intCode n
  let op := Procedure.first (cutObservationCode n) eout
  let dp := Procedure.second (cutObservationCode n) eout
  let ip := (cutIndexIP n).comp op
  let jp := (cutIndexJP n).comp op
  let qp := (cutThresholdP n).comp op
  let less := (cutLessP n).comp op
  let greater := (cutGreaterP n).comp op
  let fl := Procedure.ratFloor.comp qp
  let ce := OracleSpec.Arithmetic.ratCeil.comp qp
  let one := Procedure.constant ea intCode (1:ℤ)
  let cl := Procedure.intSub.comp (ce.pair one)
  let cg := Procedure.intNeg.comp (Procedure.intAdd.comp (fl.pair one))
  let pl := tightenP ea (i := fun x => x.1.j) (j := fun x => x.1.i) dp jp ip cl
  let pg := tightenP ea (i := fun x => x.1.i) (j := fun x => x.1.j) dp ip jp cg
  let pe₁ := tightenP ea (i := fun x => x.1.j) (j := fun x => x.1.i) dp jp ip fl
  let pe := tightenP ea (i := fun x => x.1.i) (j := fun x => x.1.j) pe₁ ip jp
    (Procedure.intNeg.comp fl)
  let integral := OracleSpec.Arithmetic.ratLe.comp (qp.pair (Procedure.intToRat.comp fl))
  let noneCase := Procedure.constant ea (optionCode eout) (none : Option (Bounds n))
  let eqCase := Procedure.conditional integral ((someP eout).comp pe) noneCase
  apply (Procedure.conditional less ((someP eout).comp pl)
    (Procedure.conditional greater ((someP eout).comp pg) eqCase)).congrFun
  rintro ⟨⟨i,j,q,s⟩,d⟩
  change (if decide (s = .lt) then some (tightenArc d j i (⌈q⌉-1)) else
    if decide (s = .gt) then some (tightenArc d i j (-(⌊q⌋+1))) else
    if decide (q ≤ (⌊q⌋:ℤ)) then some (tightenArc (tightenArc d j i ⌊q⌋) i j (-⌊q⌋))
    else none) = _
  have heq : q ≤ (⌊q⌋:ℤ) ↔ q = (⌊q⌋:ℤ) := ⟨fun h => le_antisymm h (Int.floor_le _), Eq.le⟩
  cases s <;> simp [addObservation, heq]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
