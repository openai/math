import OAI.Optimization.LinearProgramming.Lattice.BitRadixGrowth
import OAI.Optimization.LinearProgramming.Lattice.BitSelectorConstants
import OAI.Optimization.LinearProgramming.Lattice.RadixRAMCell
import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment

/-! The final signed radix vector is also computed by a uniform finite bit program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Horner
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- Public dimension, public unary radix width, then newest-first signed digit rows. -/
abbrev Input := (ℕ × ℕ) × IntMatrix
def inputCode := prodCode (prodCode unaryCode unaryCode) intMatrixCode

def assembleWord (x : Input) : List ℤ :=
  x.2.reverse.foldl (step ((2:ℤ)^x.1.2)) (List.replicate x.1.1 0)

noncomputable def pushP : Procedure (prodCode intRowCode foldStateCode) foldStateCode push := by
  let code := prodCode intRowCode foldStateCode
  let s := second intRowCode foldStateCode
  let B := (first intCode intRowCode).comp s
  let v := (second intCode intRowCode).comp s
  let d := first intRowCode foldStateCode
  exact B.pair (Driver.combineRowsP.comp ((B.pair (constant code intCode (-1))).pair (v.pair d)))

noncomputable def foldP : Procedure (prodCode intMatrixCode foldStateCode) foldStateCode
    (fun x => x.1.foldl (fun s r => push (r,s)) x.2) :=
  foldList ([] : List ℤ) pushP (Polynomial.C 32*(Polynomial.X+3)^3) prefix_words

/-- Explicit word Horner loop with an input-sized iteration count and a proved polynomial
bound on every word held by the underlying repeated procedure. -/
noncomputable def assembleWordP : Procedure inputCode intRowCode assembleWord := by
  let shape := first (prodCode unaryCode unaryCode) intMatrixCode
  let dim := (first unaryCode unaryCode).comp shape
  let width := (second unaryCode unaryCode).comp shape
  let B := natToInt.comp (Selector.powTwoP.comp width)
  let zero := constant (prodCode unaryCode inputCode) intCode (0:ℤ)
  let zeros := (tabulate (f:=fun (_ : Input) (_ : ℕ) => (0:ℤ)) 0 zero).comp (dim.pair (identity inputCode))
  let rows := (listReverse (ea:=intRowCode) ([]:List ℤ)).comp (second (prodCode unaryCode unaryCode) intMatrixCode)
  let answer := (second intCode intRowCode).comp (foldP.comp (rows.pair (B.pair zeros)))
  refine answer.congrFun ?_
  intro x
  change ((x.2.reverse.foldl (fun s r => push (r,s))
    (((2^x.1.2:ℕ):ℤ),(List.range x.1.1).map (fun _ => (0:ℤ))))).2 = _
  rw [fold_state]
  simp [assembleWord]

theorem forwardFold_pack {p : ℕ} (B : ℤ) (zs : List (Fin p → ℤ)) :
    (zs.map List.ofFn).foldl (step B) (List.replicate p 0) = List.ofFn (radixVector B zs) := by
  induction zs using List.reverseRecOn with
  | nil => exact (List.ofFn_const p (0:ℤ)).symm
  | append_singleton zs z ih =>
    simp only [List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    rw [step,Driver.combineRows_pack]
    apply congrArg List.ofFn
    funext i
    rw [RadixRAM.radixVector_append_digit]
    simp

theorem assembleWordPack {p : ℕ} (w : ℕ) (old : List (Fin p → ℤ)) :
    assembleWord ((p,w),old.map List.ofFn) = List.ofFn (radixVector ((2:ℤ)^w) old.reverse) := by
  change (old.map List.ofFn).reverse.foldl _ _ = _
  rw [← List.map_reverse]
  exact forwardFold_pack _ _

/-- A physical deployment with no oracle calls computes the final packed row from exactly
the public shape and the newest-first digit stream. -/
theorem assembleMachinePack (o : OracleSpec.WordOracle) {p : ℕ} (w : ℕ) (old : List (Fin p → ℤ)) :
    let input := inputCode ((p,w),old.map List.ofFn)
    (OracleSpec.BitCode.deploy assembleWordP).ComputesWithin o input
      (3*assembleWordP.bound.eval input.length+2*input.length+2)
      (fun h word => h=[] ∧ word=intRowCode (List.ofFn (radixVector ((2:ℤ)^w) old.reverse))) := by
  simpa only [assembleWordPack] using
    OracleSpec.BitCode.deploy_correct assembleWordP o ((p,w),old.map List.ofFn)

end Horner
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
