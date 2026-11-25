import OAI.Computability.NearSquareRoot.InterchangeBQuestBank
import OAI.Computability.NearSquareRoot.InterchangeRepairRun

/-!
# Bounded bank operations for the Hermite correction

The grouping and linear scans of the repair schedule use the same physical
store as the time-only implementation. Each branch here tracks the stack
space of the original bank and the retained outputs during recursive work.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.BRepairRun

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.InterchangeSpace RepairRun SwapRepair

variable {I Y E A B C : Type} {X : I → Type} {r : Regime I} {N l : I → ℕ}
    {job : Job Y} {zone : I → Y → Prop}

/-- All input and output register orders are available to the caller. -/
def Runs (job : Job Y) (r : Regime I) (N l : I → ℕ) (zone : I → Y → Prop)
    (cell : Cell X E) (k : ℕ) (x : Values X A E) (y : Values X B E) : Prop :=
  ∀ sa : Series A, ∀ sb : Series B,
    BHop job r N l zone k (together r.header (render cell sa x)) (render cell sb y)

variable {cell : Cell X E} (store : Store r N l cell)
    {x : Values X A E} {y : Values X B E} {z : Values X C E} {p q : ℕ}

include store

theorem runs_table [Fintype A] [Fintype B] [Nonempty A] (x : Values X A E) (f : (A → E) → B → E) :
    Runs job r N l zone cell 0 x (fun i b u => f (fun a => x i a u) b) :=
  fun sa sb => BHop.tarry (store.table sa sb x f)

theorem Runs.seq [Fintype B] (h : Runs job r N l zone cell p x y)
    (g : Runs job r N l zone cell q y z) : Runs job r N l zone cell (p+q) x z := by
  let middle := Series.arbitrary B
  intro sa sc
  simpa only [Nat.cast_add] using BHop.sequence store.positive (liveBank store sa x)
    (liveBank store middle y) (h sa middle) (g middle sc)

open private merge from OAI.Computability.NearSquareRoot.InterchangeRepairRun

theorem Runs.fork [Fintype B] [Fintype C] (h : Runs job r N l zone cell p x y)
    (g : Runs job r N l zone cell q x z) : Runs job r N l zone cell (p+q) x (both y z) := by
  let b := Series.arbitrary B
  let c := Series.arbitrary C
  intro sa out
  have run := (h sa b).doubleg (g sa c)
    (Rip.alivePair (Drive.started store.positive) (liveBank store sa x)) (liveBank store b y) (liveBank store c z)
  simpa only [Nat.cast_add] using run.afterTask (merge store b c out y z)

theorem empty_target [IsEmpty B] (x : Values X A E) (y : Values X B E) :
    Runs job r N l zone cell 0 x y := by
  intro sa sb
  apply BHop.tarry
  exact Fatigue.dry sb _ (Rip.alivePair (Drive.started store.positive) (liveBank store sa x))
    (fun b => isEmptyElim b)

theorem Runs.keep [Fintype A] [Fintype B] (h : Runs job r N l zone cell p x y) :
    Runs job r N l zone cell p x (both x y) := by
  have saved : Runs job r N l zone cell 0 x x := by
    by_cases ha : Nonempty A
    · exact runs_table store x (fun u a => u a)
    · have : IsEmpty A := not_nonempty_iff.mp ha
      exact empty_target store x x
  simpa only [Nat.zero_add] using saved.fork store h

theorem runs_rows [Fintype A] (F : (i : I) → (X i → E) → X i → E) (x : Values X A E)
    (step : ∀ v : (i : I) → X i → E, BHop job r N l zone p
      (together r.header (fun i => cell i (v i))) (fun i => cell i (F i (v i)))) :
    Runs job r N l zone cell (Fintype.card A*p) x (fun i a => F i (x i a)) := by
  intro sa sb
  have h := BHop.collect store.positive sa sb (fun i a => cell i (x i a))
    (fun i a => cell i (F i (x i a))) id (fun _ => p)
    (fun a => store.live (fun i => x i a)) (fun a => store.live (fun i => F i (x i a)))
    (fun a => step (fun i => x i a))
  change BHop job r N l zone _ (together r.header (stackRun (fun _ => sa) (fun i a => cell i (x i a))))
    (stackRun (fun _ => sb) (fun i a => cell i (F i (x i a))))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul] using h

/-- The finite coefficient lookup may depend on the mask of the current address. -/
def Tagged {K : Type} [Field K] {m : ℕ} (job : Job Y) (r : Regime I) (N l : I → ℕ)
    (zone : I → Y → Prop) (enc : Cell X (Coeff K m)) (tag : (i : I) → X i → Pattern m) : Prop :=
  ∀ {S U : Type} [Fintype S] [Fintype U] [Nonempty S] (v : Values X S (Coeff K m))
    (f : Pattern m → (S → Coeff K m) → U → Coeff K m),
    Runs job r N l zone enc 0 v (fun i t a => f (tag i a) (fun k => v i k a) t)

end Interchange.BRepairRun

end NearSquareRoot
end Computability
end OAI
