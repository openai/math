import OAI.Optimization.LinearProgramming.Lattice.BitSelectorConstants
import OAI.Optimization.LinearProgramming.Lattice.OracleRows

/-! A denominator-clearing program shared by the rational projector and the graph basis. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Selector
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B C : Type} {ea : A → List Bool} {eb : B → List Bool} {ec : C → List Bool}

private theorem map_indices (d : A) (xs : List A) (f : A → B) :
    (List.range xs.length).map (fun i => f (readAt d xs i)) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i hi _
  have hi' : i < xs.length := by simpa using hi
  simp [readAt,List.head?_drop,hi']

/-- Map over a framed list while keeping a second, fixed input available for every entry. -/
noncomputable def mapWithContextP {xs : C → List A} {f : C → A → B} (da : A) (db : B)
    (source : Procedure ec (listCode ea) xs)
    (body : Procedure (prodCode ea ec) eb (fun x => f x.2 x.1)) :
    Procedure ec (listCode eb) (fun c => (xs c).map (f c)) := by
  let ctx := second Nat.bits ec
  let entry := getAtP da (source.comp ctx) (first Nat.bits ec)
  let loop := tabulateBinaryAlongP (ed:=eb) (cell:=fun c i => f c (readAt da (xs c) i))
    da db source (body.comp (entry.pair ctx))
  exact loop.congrFun (fun c => map_indices da (xs c) (f c))

abbrev RatTable := List (List ℚ)
def ratTableCode := listCode vectorCode

def rowDenominatorList (row : List ℚ) : ℕ := (row.map Rat.den).prod
def matrixDenominatorList (A : RatTable) : ℕ := (A.map rowDenominatorList).prod
def scaledInteger (D : ℕ) (q : ℚ) : ℤ := (D/q.den : ℕ)*q.num

def integralRowsList (A : RatTable) : IntMatrix :=
  A.map fun row => row.map (scaledInteger (matrixDenominatorList A))

def packedTable {α : Type} {n p : ℕ} (P : Fin n → Fin p → α) : List (List α) :=
  List.ofFn fun i => List.ofFn (P i)

theorem matrixDenominatorListPack {n p : ℕ} (P : Fin n → Fin p → ℚ) :
    matrixDenominatorList (packedTable P) = matrixDenominator P := by
  simp [matrixDenominatorList,packedTable,matrixDenominator,rowDenominatorList,List.map_ofFn,List.prod_ofFn,Function.comp_def]

theorem integralRowsListPack {n p : ℕ} (P : Fin n → Fin p → ℚ) :
    integralRowsList (packedTable P) = packedTable (integralRows P) := by
  unfold integralRowsList
  rw [matrixDenominatorListPack]
  simp only [packedTable,List.map_ofFn,Function.comp_def]
  rfl

noncomputable def rowDenominatorListP : Procedure vectorCode Nat.bits rowDenominatorList :=
  natProductP.comp (listMap (0:ℚ) (0:ℕ) ratDen)

noncomputable def matrixDenominatorListP : Procedure ratTableCode Nat.bits matrixDenominatorList :=
  natProductP.comp (listMap ([] : List ℚ) (0:ℕ) rowDenominatorListP)

noncomputable def scaledIntegerP : Procedure (prodCode ratCode Nat.bits) intCode
    (fun x => scaledInteger x.2 x.1) := by
  let q := first ratCode Nat.bits
  let quotient := binaryDiv.comp ((second ratCode Nat.bits).pair (ratDen.comp q))
  exact intMul.comp ((natToInt.comp quotient).pair (ratNum.comp q))

noncomputable def clearRowP : Procedure (prodCode vectorCode Nat.bits) intRowCode
    (fun x => x.1.map (scaledInteger x.2)) := by
  let code := prodCode vectorCode Nat.bits
  let row := first vectorCode Nat.bits
  let scale := (second vectorCode Nat.bits).comp (second ratCode code)
  exact mapWithContextP (0:ℚ) (0:ℤ) row
    (scaledIntegerP.comp ((first ratCode code).pair scale))

/-- Convert a whole rational table to signed integers using a common positive denominator.
The procedure accepts rows of any length. On a rectangular input its output is precisely
the finite-matrix denominator clearing used by the sign oracle and rational LLL. -/
noncomputable def integralRowsListP : Procedure ratTableCode intMatrixCode integralRowsList := by
  let code := prodCode ratTableCode Nat.bits
  let rows := first ratTableCode Nat.bits
  let scale := (second ratTableCode Nat.bits).comp (second vectorCode code)
  let row := clearRowP.comp ((first vectorCode code).pair scale)
  let loop := mapWithContextP (eb:=intRowCode)
    (f:=fun (c : RatTable × ℕ) (r : List ℚ) => r.map (scaledInteger c.2)) ([]:List ℚ) ([]:List ℤ) rows row
  exact loop.comp ((identity ratTableCode).pair matrixDenominatorListP)

end Selector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
