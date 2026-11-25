import OAI.Optimization.LinearProgramming.Lattice.BitTables
import OAI.Optimization.LinearProgramming.Lattice.BitProbeTypes
import OAI.Optimization.LinearProgramming.Lattice.Bisection

/-! Pure binary instructions for forming and orienting every emitted integral row. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Combination := (ℤ × ℤ) × (Row × Row)
def coeffCode := prodCode intCode intCode
def combinationCode : Combination → List Bool := prodCode coeffCode rowPairCode

def combineCell (c : Combination) (j : ℕ) : ℤ :=
  c.1.1*readAt 0 c.2.1 j - c.1.2*readAt 0 c.2.2 j

def combineRows (c : Combination) : Row := (List.range c.2.1.length).map (combineCell c)

noncomputable def combineRowsP : Procedure combinationCode intRowCode combineRows := by
  let coeff := first coeffCode rowPairCode
  let rows := second coeffCode rowPairCode
  let u := (first intCode intCode).comp coeff
  let v := (second intCode intCode).comp coeff
  let a := (first intRowCode intRowCode).comp rows
  let b := (second intRowCode intRowCode).comp rows
  let ctx := second Nat.bits combinationCode
  let idx := first Nat.bits combinationCode
  let ua := intMul.comp ((u.comp ctx).pair (getAtP 0 (a.comp ctx) idx))
  let vb := intMul.comp ((v.comp ctx).pair (getAtP 0 (b.comp ctx) idx))
  let cell := intSub.comp (ua.pair vb)
  exact tabulateBinaryAlongP 0 0 a cell

theorem combineRows_pack {p : ℕ} (r s : ℤ) (a b : Fin p → ℤ) :
    combineRows ((r,s),(List.ofFn a,List.ofFn b)) = List.ofFn (fun i => r*a i - s*b i) := by
  have hr {α : Type} (f : ℕ → α) : (List.range p).map f = List.ofFn (fun i : Fin p => f i.val) := by
    apply List.ext_getElem <;> simp
  simp [combineRows,hr,combineCell]

noncomputable def negateRowP : Procedure intRowCode intRowCode (List.map Neg.neg) :=
  listMap (0:ℤ) (0:ℤ) intNeg

theorem negateRow_pack {p : ℕ} (a : Fin p → ℤ) :
    (List.ofFn a).map Neg.neg = List.ofFn (-a) := by
  simp [List.map_ofFn,Function.comp_def]
  rfl

def rowDifference (r : Row × Row) : Row := combineRows ((1,1),r)

noncomputable def rowDifferenceP : Procedure rowPairCode intRowCode rowDifference :=
  combineRowsP.comp ((constant rowPairCode coeffCode (1,1)).pair (identity rowPairCode))

theorem rowDifference_pack {p : ℕ} (a b : Fin p → ℤ) :
    rowDifference (List.ofFn a,List.ofFn b) = List.ofFn (a-b) := by
  simp [rowDifference,combineRows_pack]
  rfl

theorem dyadic_combine_pack {p : ℕ} (a b : Fin p → ℤ) (k : ℕ) (n : ℤ) :
    combineRows ((2^k,n),(List.ofFn a,List.ofFn b)) = List.ofFn (dyadicQuery a b k n) :=
  combineRows_pack _ _ _ _

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
