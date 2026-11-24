import OAI.Computability.VPVNP.RankCursorSchur
import OAI.Computability.VPVNP.RankQueryStackEngineSpace

/-! # Rank-cursor queries with separate time and space for scalar entries

A streamed matrix-entry computation can use exponential time and polynomial
space. The caller retains the descriptor's own stack cap, while its time
bound enters the running time of the Schur recursion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch

/-- Step bound for one Schur coefficient query, charging the entry descriptor’s time allowance
at each recursive engine step. -/
def readClock (n U Z Bd B w v e : ℕ) :=
  loadClock w + (SchurKey.clock n U Z * Engine.boundedStepTime Bd B w v e + 1)

/-- Stack-height bound for one Schur coefficient query using the entry descriptor’s separate
peak-space allowance S. -/
def readSpace (n U S A B w v e : ℕ) :=
  max (max w A + loadClock w) (Engine.boundedSpace S A (Nat.clog 2 U+4+Nat.clog 2 n) B w v e)

theorem readClock_le (n U Z Bd B w v e s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s) :
    readClock n U Z Bd B w v e ≤
      loadClock w + (2^((2*s+8)*(2*s+5)) * Engine.boundedStepTime Bd B w v e + 1) :=
  Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_right _ (SchurKey.clock_le_exp n U Z s hn hu hz)) _) _

theorem readSpace_le (n U S A B w v e s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) :
    readSpace n U S A B w v e ≤
      max (max w A + loadClock w) (Engine.boundedSpace S A (2*s+4) B w v e) := by
  have h₁ := Nat.clog_le_of_le_pow hn
  have h₂ := Nat.clog_le_of_le_pow hu
  have hd : Nat.clog 2 U + 4 + Nat.clog 2 n ≤ 2*s+4 := by omega
  exact max_le_max le_rfl (max_le_max le_rfl (Nat.add_le_add_right
    (max_le_max le_rfl (max_le_max le_rfl (Nat.mul_le_mul_right _ hd))) _))

variable {K : Type} [DecidableEq K] {n U Z p e w v A B Bd S : ℕ} {c : SliceArithmetic.Vector p e}
variable [Fact p.Prime] [NeZero e] {a : Engine.Actions K} {entry : Entry n (Scalar c)}
variable {ready : Stacks K → Prop} {pending : SchurKey n U Z → Stacks K → Prop}

/-- Use the descriptor time only in the total clock. Its certified stack cap,
together with the live register and return stack caps, suffices throughout. -/
theorem rootQuery_separate
    (spec : Engine.Contracts a (SchurKey.program (U := U) (Z := Z) entry) w v B
      (SchurKey.arityBound n U Z) ready pending Bd)
    (desc : Engine.DescribeBounded a (SchurKey.program (U := U) (Z := Z) entry) w v Bd S
      (Nat.clog 2 U+4+Nat.clog 2 n) ready)
    (ha : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (M : Matrix (Fin n) (Fin n) (Polynomial (Scalar c))) (he : ∀ i j k, entry i j k = (M i j).coeff k)
    (persistent : Word w) (rs : Regs Registers.R w) (u : Limit U) (z : Limit Z)
    (hregs : Registers.Stores rs Z u.val z.val) (aux : Stacks K) (haux : ready aux) :
    ∃ t ≤ readClock n U Z Bd B w v e, ∃ out, ready out ∧
      (rootQuery a).BoundedRun (readSpace n U S A B w v e) t (scanBank n persistent rs [] (idle aux))
        (scanBank n persistent rs [] (yielded out (Engine.scalar v ((M.charpolyRev.coeff u.val).coeff z.val)))) := by
  obtain ⟨ticks, ht, out, ho, engine⟩ := Engine.eval_root_bounded spec desc ha M he u z aux haux
  exact ⟨_, Nat.add_le_add_left ht _, out, ho,
    routeRoot_bounded persistent rs u z hregs aux out (ha aux haux) _ engine⟩

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
