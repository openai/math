import OAI.Computability.VPVNP.RankQueryStackGramSpace
import OAI.Computability.VPVNP.RankQueryDescribeSpace

/-!
# End-to-end determinant coefficient query on a streamed relation matrix

The independent height bound of the matrix-entry reader is reused through
every recursive call. The entry reader's running time only enters the clock.
The answer is the bivariate coefficient of the reverse characteristic
polynomial of the weighted Gram matrix over the native extension-field ring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.GramEngine

open Engine RAMTape Dispatch

variable {K : Type} [DecidableEq K] {w v d p e n m U Z B A S depth : ℕ}
variable [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- Stack-height bound while decoding a Schur query, including its suspended frames and the
Gram entry reader. -/
def descriptorSpace (w v e A S depth : ℕ) :=
  max (entryCap w v e A depth) (DescribeAdapter.space w v e (entryCap w v e A depth) S)

theorem describeBounded (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {readerReady : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S readerReady)
    (ha : ∀ s, readerReady s → ∀ i, (s i).length ≤ A)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hw : (d+1)*widthFactor ≤ w)
    (hd : d ≤ w) (hsize : n+U+Z+m+8 < 2^d) :
    DescribeBounded (actions read) (SchurKey.program (U := U) (Z := Z) (weightedGramEntryCoeff M)) w v
      (DescribeAdapter.clock w v e B) (descriptorSpace w v e A S depth) depth (Ready w v n m c readerReady) :=
  lift_bounded ha (DescribeAdapter.describe_bounded read M hc hv hw₃ hw hd hsize)

/-- Bit-stack step bound for a Schur coefficient query, using the recursion depth, branching
bound, and entry-reader clock `B`. -/
def queryTime (n U Z w v e B : ℕ) :=
  (5+6*SchurKey.arityBound n U Z)^(Nat.clog 2 U+4+Nat.clog 2 n+1) *
    boundedStepTime (DescribeAdapter.clock w v e B) (Assembly.localBudget w e v) w v e + 1

/-- Maximum stack height during a Gram coefficient query, including its recursive frames and
the entry reader's workspace. -/
def querySpace (n U w v e A S : ℕ) :=
  let depth := Nat.clog 2 U+4+Nat.clog 2 n
  boundedSpace (descriptorSpace w v e A S depth) (w+v+e+e*v+A) depth (Assembly.localBudget w e v) w v e

/-- The physical root subroutine performs its own Schur recursion and scalar
arithmetic. Its caller supplies a bounded entry routine for the original
matrix. The query's two coefficient indices may vary between calls. -/
theorem root_query (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {readerReady : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S readerReady)
    (ha : ∀ s, readerReady s → ∀ i, (s i).length ≤ A)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hw : (d+1)*widthFactor ≤ w)
    (hd : d ≤ w) (hsize : n+U+Z+m+8 < 2^d)
    (s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s) (hs : 2*s+6 ≤ w) (hws : (2*s+6+1)*widthFactor ≤ w)
    (u : Limit U) (z : Limit Z) (aux : Stacks (Aux K)) (haux : Ready w v n m c readerReady aux) :
    ∃ t ≤ queryTime n U Z w v e B, ∃ out, Ready w v n m c readerReady out ∧
      (machine read).BoundedRun (querySpace n U w v e A S) t
        (atControl (c := c) w v (.enter (SchurKey.root (n := n) u z)) [] aux)
        (atControl w v (.returned (((weightedGram M).charpolyRev.coeff u.val).coeff z.val)) ([] : List (F n U Z c)) out) :=
  eval_root_bounded (contracts read M hc.correct hv hw₃ hw hd hsize s hn hu hz hs hws)
    (describeBounded read M hc ha hv hw₃ hw hd hsize) (fun _ hr => ready_length hr ha)
    (weightedGram M) (weightedGramEntryCoeff_eq M) u z aux haux

end RankQuery.Stack.GramEngine

end VPVNP
end Computability
end OAI
