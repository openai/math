import OAI.Computability.VPVNP.RankCursorMachine
import OAI.Computability.VPVNP.RankCursorSchur

/-! # Full rectangular rank query on the determinant stack

A single finite control traverses the rectangle of bidegrees. At each
request it stages the six fields of the weighted Gram determinant, executes
the Schur engine, tests the returned scalar, and advances or terminates.
The result register contains the rank of the original rectangular matrix
over the advised field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch

variable {K : Type} [DecidableEq K] {n m w v A B b p e : ℕ}
    [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- Run the rectangular rank scan with the Schur engine's root query at each bidegree and leave
the resulting rank in the cursor registers. -/
def fullRank (a : Engine.Actions K) : FiniteRoutine (ScanPort K) := rankMachine (rootQuery a)

/-- Step bound for scanning an `n` by `m` matrix. It allows a Schur root query and cursor check
at each of the `(n+1)*((n+m)*n+1)` bidegrees. -/
def rankTime (n m B w v e : ℕ) :=
  let Z := (n+m)*n
  ((n+1)*(Z+1))*(rootQueryClock n n Z B w v e+checkClock w v e+1)+2

/-- The rectangular query's only engine hypotheses specify the concrete
dispatch, entry, and arithmetic routines. No rank-oracle hypothesis enters
the scan or the decision to stop. -/
theorem fullRank_runs [Fact (Irreducible (SliceArithmetic.modulus c))]
    (a : Engine.Actions K) (M : Matrix (Fin n) (Fin m) (Scalar c))
    (ready : Stacks K → Prop) (pending : SchurKey n n ((n+m)*n) → Stacks K → Prop)
    (spec : Engine.Contracts a (SchurKey.program (U := n) (Z := (n+m)*n) (weightedGramEntryCoeff M))
      w v B (SchurKey.arityBound n n ((n+m)*n)) ready pending)
    (hcap : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (hwidth : (b+1)*control.wordFactor ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (hsize : max 1 (max n ((n+m)*n)) < 2^b)
    (persist : Word w) (rs : Regs Registers.R w) (aux : Stacks K) (haux : ready aux)
    (hr : Registers.Stores rs ((n+m)*n) n ((n+m)*n)) :
    ∃ k ≤ rankTime n m B w v e, ∃ out a', ready a' ∧
      Registers.Stores out ((n+m)*n) (M.map (Scalar.interpretation c)).rank 0 ∧
      (fullRank a).Runs k (scanBank n persist rs [true] (idle aux)) (scanBank n persist out [] (idle a')) := by
  let Z := (n+m)*n
  apply rankMachine_runs (rootQuery a) M ready (rootQueryClock n n Z B w v e) _ hwidth hv hsize
    persist rs aux haux hr
  intro u z hu hz p₀ rs₀ aux₀ hrs hready
  let i : Limit n := ⟨u, Nat.lt_succ_of_le hu⟩
  let j : Limit Z := ⟨z, Nat.lt_succ_of_le hz⟩
  have h := rootQuery_runs spec hcap (weightedGram M) (weightedGramEntryCoeff_eq M)
    p₀ rs₀ i j hrs aux₀ hready
  rw [SchurKey.compute_correct (weightedGram M) _ (weightedGramEntryCoeff_eq M) u z]
  exact h

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
