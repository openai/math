import OAI.Computability.VPVNP.MacaulayReadRouter
import OAI.Computability.VPVNP.CoordinateQueries

/-!
# Macaulay readers for prefix rank queries

The greedy row scan reads a row prefix at its original addresses. The
column scan uses the same reader with row and column ports interchanged.
Renaming these ports preserves the exact instruction trace, including its
time and live stack-height bounds.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead

open RAMTape

variable {K : Type} {p e n m w v B S : ℕ} {c : SliceArithmetic.Vector p e}

private def swapAddress : Port K → Port K
  | .row => .col
  | .col => .row
  | .result => .result
  | .aux k => .aux k

private theorem swapAddress_involutive : Function.Involutive (swapAddress (K := K)) := by
  intro k; cases k <;> rfl

/-- The coefficient routine of the transposed matrix, with its usual caller
convention. Only the physical addresses of its row and column ports change. -/
def transpose (read : FiniteRoutine (Port K)) : FiniteRoutine (Port K) :=
  read.onPorts swapAddress

/-- Retain the first `r` rows of a matrix of encoded scalars. -/
abbrev prefixMatrix {R : Type*} (A : Matrix (Fin n) (Fin m) R) (r : ℕ) (hr : r ≤ n) :=
  RankQuery.prefixRows A r hr

/-- Applying any scalar interpretation before or after restricting to the
prefix yields exactly the matrix in the greedy rank formula. -/
theorem map_prefixMatrix {R F : Type*} (A : Matrix (Fin n) (Fin m) R) (r : ℕ) (hr : r ≤ n)
    (f : R → F) :
    (prefixMatrix A r hr).map f = RankQuery.prefixRows (A.map f) r hr := rfl

/-- On the column scan the interpreted matrix is transposed before taking
the row prefix. -/
theorem map_prefixMatrix_transpose {R F : Type*} (A : Matrix (Fin n) (Fin m) R) (r : ℕ) (hr : r ≤ m)
    (f : R → F) :
    (prefixMatrix A.transpose r hr).map f = RankQuery.prefixRows (A.map f).transpose r hr := rfl

variable [DecidableEq K] {read : FiniteRoutine (Port K)} {M : Matrix (Fin n) (Fin m) (Scalar c)}
    {ready : Stacks K → Prop}

/-- Every original entry query gives one transpose query with exactly the
same cost, final auxiliary bank, and peak storage allowance. -/
theorem CorrectSpace.transpose (h : CorrectSpace read M w v B S ready) :
    CorrectSpace (MacaulayRead.transpose read) M.transpose w v B S ready := by
  intro i j aux hs
  obtain ⟨t, ht, out, ho, run⟩ := h j i aux hs
  refine ⟨t, ht, out, ho, ?_⟩
  apply FiniteRoutine.BoundedRun.framed swapAddress_involutive.injective run
  · intro k
    have hh := run.initial_cap (swapAddress k)
    cases k <;> exact hh
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro k hk
    exact (hk (swapAddress k) (swapAddress_involutive k)).elim

/-- The ordinal of a row in a prefix is already its address in the original
matrix. No instructions or additional stack cells are required. -/
theorem CorrectSpace.prefixMatrix (h : CorrectSpace read M w v B S ready) (r : ℕ) (hr : r ≤ n) :
    CorrectSpace read (prefixMatrix M r hr) w v B S ready :=
  fun i j aux ok => h (Fin.castLE hr i) j aux ok

/-- The complete calling convention used for prefix ranks of the transpose. -/
theorem CorrectSpace.transpose_prefix (h : CorrectSpace read M w v B S ready) (r : ℕ) (hr : r ≤ m) :
    CorrectSpace (MacaulayRead.transpose read) (MacaulayRead.prefixMatrix M.transpose r hr) w v B S ready :=
  h.transpose.prefixMatrix r hr

/-- The concrete three-way reader also accepts each transpose prefix with
the bounds established for the routed equation, affine, and power arms. -/
theorem reader_transpose_prefix
    {arms : MacaulayRowDispatch.Kind → FiniteRoutine (Bus K)}
    {leafReady : Stacks (Work K) → Prop}
    (h : CorrectSpace (reader arms) M w v B S leafReady) (r : ℕ) (hr : r ≤ m) :
    CorrectSpace (transpose (reader arms)) (MacaulayRead.prefixMatrix M.transpose r hr) w v B S leafReady :=
  h.transpose_prefix r hr

end RankQuery.Stack.MacaulayRead

end VPVNP
end Computability
end OAI
