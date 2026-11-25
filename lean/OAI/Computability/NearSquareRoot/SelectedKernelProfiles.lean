import OAI.Computability.NearSquareRoot.FixedCandidateJointParameters
import OAI.Computability.NearSquareRoot.PhysicalKernelProfiles
import OAI.Computability.NearSquareRoot.SelectedPhysicalKernel

/-! # The six physical source files on the common effective parameter tuple

The scheduler enumerates every tuple. Eventual inequalities on the three
reserve parameters serve to identify one simultaneous comparison for each
requested exponent. They do not enter its executable control.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CandidateParameters

open IntegerMultiplication Code DigitPacking FixedPoint FixedLayer
  SynchronizedLayers SynchronizedPermutationBudget Filter KernelPass.ComputableSyntax

/-- Choose the low reserve, high reserve and exterior mask reserve successively. -/
def EventuallyReserves (j : ℕ) (pred : Guess → Prop) : Prop :=
  ∀ᶠ a : ℕ in atTop, ∀ᶠ b : ℕ in atTop, ∀ᶠ D : ℕ in atTop, pred (j,a,b,D)

theorem EventuallyReserves.and {j : ℕ} {P Q : Guess → Prop}
    (hp : EventuallyReserves j P) (hq : EventuallyReserves j Q) :
    EventuallyReserves j (fun p => P p ∧ Q p) := by
  filter_upwards [hp,hq] with a aP aQ
  filter_upwards [aP,aQ] with b bP bQ
  exact bP.and bQ

theorem EventuallyReserves.of_forall {j : ℕ} {P : Guess → Prop} (h : ∀ a b d,P (j,a,b,d)) :
    EventuallyReserves j P :=
  Eventually.of_forall (fun a => Eventually.of_forall fun b => Eventually.of_forall fun d => h a b d)

theorem EventuallyReserves.mono {j : ℕ} {P Q : Guess → Prop}
    (hp : EventuallyReserves j P) (h : ∀ p,P p → Q p) : EventuallyReserves j Q := by
  filter_upwards [hp] with a ha
  filter_upwards [ha] with b hb
  filter_upwards [hb] with d hd
  exact h (j,a,b,d) hd

theorem EventuallyReserves.choose {j : ℕ} {P : Guess → Prop} (h : EventuallyReserves j P) :
    ∃ p : Guess, exponent p = j ∧ P p := by
  obtain ⟨a,ha⟩ := h.exists
  obtain ⟨b,hb⟩ := ha.exists
  obtain ⟨d,hd⟩ := hb.exists
  exact ⟨(j,a,b,d),rfl,hd⟩

private theorem allReserves {L : Type} {j : ℕ} (l : List L) (P : L → Guess → Prop)
    (h : ∀ k ∈ l, EventuallyReserves j (P k)) :
    EventuallyReserves j (fun p => ∀ k ∈ l, P k p) := by
  induction l with
  | nil => exact .of_forall (fun _ _ _ k hk => (List.not_mem_nil hk).elim)
  | cons k tail ih =>
    have rest := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact ((h k (List.mem_cons_self ..)).and rest).mono (fun p good b hb => by
      rcases List.mem_cons.mp hb with rfl|h'
      · exact good.1
      · exact good.2 b h')

/-- The run on accepted rows reads the physically present unary input length.
The validity proof uses only the computable size guard. -/
abbrev Input (degree : ℕ) (p : Guess) := LargeInput (inputCut degree p)
abbrev operandWidth (degree : ℕ) (p : Guess) (i : Input degree p) := i.val.width
/-- Source and result interface of each emitted elementary transport. -/
def SourceRun (degree : ℕ) (kind : TransportKind) (arena clock : Guess → ℕ → ℕ) : Prop :=
  match kind with
  | .crt d => EffectiveCRTAt (inputCut degree) arena clock (fun p i =>
      if d then afterInverseCRT (directory degree p i) else route (directory degree p i))
  | .permutation d => EffectiveImplementsAt (operandWidth degree) (directory degree)
      (fun _ _ => d) (axes degree) arena clock .permutation
  | .walsh d => EffectiveImplementsAt (operandWidth degree) (directory degree)
      (fun _ _ => d) (axes degree) arena clock .walsh

def GoodClock (kind : TransportKind) (j : ℕ) (ticks : ℕ → ℕ) : Prop :=
  match kind with
  | .crt _ => RouteBound (Generator.targetExponent j) ticks
  | .permutation _ | .walsh _ => RowClock (Generator.midExponent j) ticks

/-- The file is uniformly emitted across all parameter tuples. Each reserve
estimate is required only eventually at a fixed comparison index. -/
structure Procedure (degree : ℕ) (kind : TransportKind) where
  arena : Guess → ℕ → ℕ
  clock : Guess → ℕ → ℕ
  run : SourceRun degree kind arena clock
  good : ∀ j : ℕ, EventuallyReserves j (fun p => LinearArena (arena p) ∧ GoodClock kind j (clock p))

/-- A finite intersection provides a tuple at which both CRT and both
transform directions attain their certified budgets simultaneously. -/
theorem uniform_of_procedures (degree : ℕ) (procedures : ∀ k, Nonempty (Procedure degree k)) :
    UniformMultiplicationSpec := by
  classical
  let f k := (procedures k).some
  apply uniform_of_profiles (inputCut degree) (inputCut_computable _) (inputCut_ge_two _)
    (directory degree) (axes degree) (width degree)
    (fun k => (f k).arena) (fun k => (f k).clock)
  · exact (f (.crt false)).run
  · exact (f (.crt true)).run
  · exact fun d => (f (.permutation d)).run
  · exact fun d => (f (.walsh d)).run
  · intro j
    let P (k : TransportKind) (p : Guess) := LinearArena ((f k).arena p) ∧ GoodClock k j ((f k).clock p)
    obtain ⟨p,_,hs⟩ := (allReserves TransportKind.all P (fun k _ => (f k).good j)).choose
    have hp (k : TransportKind) := hs k (TransportKind.mem_all k)
    have lt : Generator.midExponent j < (1:ℝ)/2+1/(j+2:ℝ) := by
      unfold Generator.midExponent
      gcongr
      linarith [Nat.cast_nonneg (α:=ℝ) j]
    exact ⟨p,Generator.midExponent j,(by linarith [(midpoint_bounds j).1]),lt,fun k => (hp k).1,
      fun d => (hp (.crt d)).2,fun d => (hp (.permutation d)).2,fun d => (hp (.walsh d)).2⟩

end FixedCandidate.CandidateParameters

end NearSquareRoot
end Computability
end OAI
