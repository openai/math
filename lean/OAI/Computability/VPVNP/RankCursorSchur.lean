import OAI.Computability.VPVNP.RankCursorSchurFields
import OAI.Computability.VPVNP.RankQueryStackEngineRun
import OAI.Computability.VPVNP.RankQueryStackScan
import OAI.Computability.VPVNP.ParseOracleResources
import OAI.Computability.VPVNP.RoutineSpace

/-!
# Calling the Schur coefficient machine from the rank cursor

One request stages the six root fields and invokes the shared Schur engine.
The resulting scalar occupies the engine result port in its native
polynomial-basis representation. The cursor registers, dimension words and
scratch retain their ready values for the following zero test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch UniversalCountStack

variable {K : Type} [DecidableEq K]

/-- The instruction table stages a root from cursor registers and calls the
same engine at every matrix dimension and every bidegree. -/
def rootQuery (a : Engine.Actions K) : FiniteRoutine (ScanPort K) :=
  loadRoot.followedBy ((Engine.machine a).onPorts ScanPort.engine)

/-- Step bound for loading one Schur root and evaluating its coefficient, using the arity and
recursion-depth bounds of the Schur expansion. -/
def rootQueryClock (n U Z B w v e : ℕ) :=
  loadClock w + ((5 + 6*SchurKey.arityBound n U Z)^(Nat.clog 2 U + 4 + Nat.clog 2 n + 1)*
    Engine.stepBudget B w v e + 1)

/-- Stack-height bound for staging the root fields and executing the Schur recursion for a
single coefficient. -/
def rootQuerySpace (n U A B w v e : ℕ) :=
  max (max w A + loadClock w) (Engine.runSpace A (Nat.clog 2 U + 4 + Nat.clog 2 n) B w v e)

/-- Bounding all three numerical query dimensions by `s` bits gives a
single exponential number of engine transitions. -/
theorem rootQueryClock_le (n U Z B w v e s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s) :
    rootQueryClock n U Z B w v e ≤
      loadClock w + (2^((2*s+8)*(2*s+5))*Engine.stepBudget B w v e + 1) := by
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (SchurKey.clock_le_exp n U Z s hn hu hz)) _) _

/-- Only logarithms of the matrix size and outer degree enter the height of
the suspended Schur frames. -/
theorem rootQuerySpace_le (n U A B w v e s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) :
    rootQuerySpace n U A B w v e ≤
      max (max w A + loadClock w) (Engine.runSpace A (2*s+4) B w v e) := by
  have h₁ := Nat.clog_le_of_le_pow hn
  have h₂ := Nat.clog_le_of_le_pow hu
  have hd : Nat.clog 2 U + 4 + Nat.clog 2 n ≤ 2*s+4 := by omega
  exact max_le_max le_rfl (Nat.add_le_add_right
    (max_le_max le_rfl (max_le_max le_rfl (Nat.mul_le_mul_right _ hd))) _)

variable {n U Z p e w v A B : ℕ} {c : SliceArithmetic.Vector p e}
variable {a : Engine.Actions K} {entry : Entry n (Scalar c)}
variable {ready : Stacks K → Prop} {pending : SchurKey n U Z → Stacks K → Prop}

omit [DecidableEq K] in
private theorem outer_length (persistent : Word w) (rs : Regs Registers.R w) (work : Stacks (Engine.Port K))
    (k : ScanPort K) (outside : ∀ j, ScanPort.engine j ≠ k) :
    (scanBank n persistent rs [] work [] k).length ≤ w := by
  cases k with
  | engine j => exact (outside j rfl).elim
  | cursor j => simpa only [scanBank, List.length_nil, Nat.max_zero] using Registers.bank_length persistent rs [] j
  | rows | depth => exact (length_digits ..).le
  | scratch => exact Nat.zero_le _

omit [DecidableEq K] in
private theorem idle_length (persistent : Word w) (rs : Regs Registers.R w) (aux : Stacks K)
    (ha : ∀ k, (aux k).length ≤ A) (k : ScanPort K) :
    (scanBank n persistent rs [] (idle aux) [] k).length ≤ max w A := by
  by_cases he : ∃ j, ScanPort.engine j = k
  · obtain ⟨j,rfl⟩ := he
    cases j with
    | aux i => exact (ha i).trans (Nat.le_max_right ..)
    | result | condition => exact Nat.zero_le _
    | frame i => cases i <;> exact Nat.zero_le _
  · exact (outer_length persistent rs (idle aux) k (not_exists.mp he)).trans (Nat.le_max_left ..)

/-- Install any certified run of the same engine. The combined bound depends
on the engine's space certificate separately from its number of transitions. -/
theorem routeRoot_bounded {cap ticks : ℕ} (persistent : Word w) (rs : Regs Registers.R w)
    (u : Limit U) (z : Limit Z) (hregs : Registers.Stores rs Z u.val z.val)
    (aux out : Stacks K) (ha : ∀ k, (aux k).length ≤ A) (coeff : Scalar c)
    (engine : (Engine.machine a).BoundedRun cap ticks
      (Engine.atControl w v (.enter (SchurKey.root (n := n) u z)) ([] : List (Engine.F n U Z c)) aux)
      (Engine.atControl w v (.returned coeff) ([] : List (Engine.F n U Z c)) out)) :
    (rootQuery a).BoundedRun (max (max w A + loadClock w) cap) (loadClock w + ticks)
      (scanBank n persistent rs [] (idle aux))
      (scanBank n persistent rs [] (yielded out (Engine.scalar v coeff))) := by
  let space := max (max w A + loadClock w) cap
  let begin := Engine.atControl w v (.enter (SchurKey.root (n := n) u z)) ([] : List (Engine.F n U Z c)) aux
  let finish := Engine.atControl w v (.returned coeff) ([] : List (Engine.F n U Z c)) out
  let start := scanBank n persistent rs [] begin
  have hload := loadRoot_runs (c := c) (v := v) persistent rs u z hregs aux (n := n)
  have load : loadRoot.BoundedRun space (loadClock w) (scanBank n persistent rs [] (idle aux)) start :=
    spaceRun_of_steps hload (fun k =>
      (Nat.add_le_add_right (idle_length persistent rs aux ha k) _).trans (le_max_left ..))
  have bounded : (Engine.machine a).BoundedRun space ticks begin finish :=
    engine.mono_cap (le_max_right ..)
  have outside (k : ScanPort K) (hk : ∀ j, ScanPort.engine j ≠ k) : (start k).length ≤ space :=
    (outer_length persistent rs begin k hk).trans <|
      (le_max_left w A).trans ((Nat.le_add_right ..).trans (le_max_left ..))
  have call := bounded.onPorts (ports := ScanPort.engine) (fun _ _ => ScanPort.engine.inj) start outside
  have hout : installStacks ScanPort.engine start finish =
      scanBank n persistent rs [] (yielded out (Engine.scalar v coeff)) := by
    apply installStacks_frame (fun _ _ => ScanPort.engine.inj) (fun k => ?_)
    · intro k hk; cases k with | engine j => exact (hk j rfl).elim | _ => rfl
    · cases k with
      | frame j => cases j <;> rfl
      | aux | condition | result => rfl
  rw [installStacks_eq (fun _ _ => ScanPort.engine.inj) start begin (fun _ => rfl), hout] at call
  exact load.followedBy call

variable [Fact p.Prime] [NeZero e]

/-- The returned scalar is the requested formal coefficient of the reverse
characteristic polynomial. Time and stack bounds include the initial word
copies and the engine call. The external Schur actions enter through their
individual physical execution contracts. -/
theorem rootQuery_bounded
    (spec : Engine.Contracts a (SchurKey.program (U := U) (Z := Z) entry)
      w v B (SchurKey.arityBound n U Z) ready pending)
    (hcap : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (M : Matrix (Fin n) (Fin n) (Polynomial (Scalar c)))
    (he : ∀ i j k, entry i j k = (M i j).coeff k)
    (persistent : Word w) (rs : Regs Registers.R w) (u : Limit U) (z : Limit Z)
    (hregs : Registers.Stores rs Z u.val z.val) (aux : Stacks K) (haux : ready aux) :
    ∃ t ≤ rootQueryClock n U Z B w v e, ∃ out, ready out ∧
      (rootQuery a).BoundedRun (rootQuerySpace n U A B w v e) t (scanBank n persistent rs [] (idle aux))
        (scanBank n persistent rs [] (yielded out (Engine.scalar v ((M.charpolyRev.coeff u.val).coeff z.val)))) := by
  obtain ⟨ticks, ht, out, ho, engine⟩ := Engine.eval_root spec hcap M he u z aux haux
  exact ⟨_, Nat.add_le_add_left ht _, out, ho,
    routeRoot_bounded persistent rs u z hregs aux out (hcap aux haux) _ engine⟩

/-- Normal-return interface for callers that need the clock and scalar. -/
theorem rootQuery_runs
    (spec : Engine.Contracts a (SchurKey.program (U := U) (Z := Z) entry)
      w v B (SchurKey.arityBound n U Z) ready pending)
    (hcap : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (M : Matrix (Fin n) (Fin n) (Polynomial (Scalar c)))
    (he : ∀ i j k, entry i j k = (M i j).coeff k)
    (persistent : Word w) (rs : Regs Registers.R w) (u : Limit U) (z : Limit Z)
    (hregs : Registers.Stores rs Z u.val z.val) (aux : Stacks K) (haux : ready aux) :
    ∃ t ≤ rootQueryClock n U Z B w v e, ∃ out, ready out ∧
      (rootQuery a).Runs t (scanBank n persistent rs [] (idle aux))
        (scanBank n persistent rs [] (yielded out (Engine.scalar v ((M.charpolyRev.coeff u.val).coeff z.val)))) := by
  obtain ⟨t,ht,out,ho,run⟩ := rootQuery_bounded spec hcap M he persistent rs u z hregs aux haux
  exact ⟨t,ht,out,ho,run.runs⟩

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
