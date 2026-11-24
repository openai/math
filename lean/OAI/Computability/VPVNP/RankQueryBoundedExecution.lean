import OAI.Computability.VPVNP.RankQueryExecution
import OAI.Computability.VPVNP.RankQueryExecutionSpace
import OAI.Computability.VPVNP.RankCursorSchurSpace

/-! # Separate time and space in the complete rectangular rank query

All determinant root requests share a single storage allowance. In particular
an expensive scalar descriptor read is charged to the running time of the
Schur traversal while retaining its independent peak-storage certificate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch

variable {K : Type} [DecidableEq K] {n m w v e b p B Bd S A : ℕ}
    [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- Step bound for scanning Schur coefficients of an n-by-m matrix, including each coefficient
read, zero test, and cursor update. -/
def boundedRankTime (n m Bd B w v e : ℕ) :=
  let Z := (n+m)*n
  ((n+1)*(Z+1))*(readClock n n Z Bd B w v e+checkClock w v e+1)+2

/-- Stack-height bound for the full rectangular rank scan, combining the peak space of a single
coefficient read with the cursor workspace. -/
def boundedRankSpace (n S A B w v e : ℕ) :=
  outerRankSpace (readSpace n n S A B w v e) A w v e

/-- The rank is returned by the literal finite stack control. Every bit
stack respects the displayed cap throughout the entire rectangular scan. -/
theorem fullRank_boundedRun [Fact (Irreducible (SliceArithmetic.modulus c))]
    (a : Engine.Actions K) (M : Matrix (Fin n) (Fin m) (Scalar c))
    (ready : Stacks K → Prop) (pending : SchurKey n n ((n+m)*n) → Stacks K → Prop)
    (spec : Engine.Contracts a (SchurKey.program (U := n) (Z := (n+m)*n) (weightedGramEntryCoeff M))
      w v B (SchurKey.arityBound n n ((n+m)*n)) ready pending Bd)
    (desc : Engine.DescribeBounded a (SchurKey.program (U := n) (Z := (n+m)*n) (weightedGramEntryCoeff M))
      w v Bd S (Nat.clog 2 n+4+Nat.clog 2 n) ready)
    (hcap : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (hwidth : (b+1)*control.wordFactor ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (hsize : max 1 (max n ((n+m)*n)) < 2^b)
    (persist : Word w) (rs : Regs Registers.R w) (aux : Stacks K) (haux : ready aux)
    (hr : Registers.Stores rs ((n+m)*n) n ((n+m)*n)) :
    ∃ k ≤ boundedRankTime n m Bd B w v e, ∃ out a', ready a' ∧
      Registers.Stores out ((n+m)*n) (M.map (Scalar.interpretation c)).rank 0 ∧
      (fullRank a).BoundedRun (boundedRankSpace n S A B w v e) k
        (scanBank n persist rs [true] (idle aux)) (scanBank n persist out [] (idle a')) := by
  let Z := (n+m)*n
  apply rankMachine_boundedRun (rootQuery a) M ready hcap _ hwidth hv hsize persist rs aux haux hr
  intro u z hu hz p₀ rs₀ aux₀ hrs hready
  let i : Limit n := ⟨u, Nat.lt_succ_of_le hu⟩
  let j : Limit Z := ⟨z, Nat.lt_succ_of_le hz⟩
  have h := rootQuery_separate spec desc hcap (weightedGram M) (weightedGramEntryCoeff_eq M)
    p₀ rs₀ i j hrs aux₀ hready
  rw [SchurKey.compute_correct (weightedGram M) _ (weightedGramEntryCoeff_eq M) u z]
  exact h

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
