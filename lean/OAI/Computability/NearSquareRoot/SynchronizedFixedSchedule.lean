import OAI.Computability.NearSquareRoot.SynchronizedLowerProgram
import OAI.Computability.NearSquareRoot.SynchronizedScheduleSemantics

/-! # Preparing parallel short-transform instructions from unary radix exponents

One fixed machine builds the local restored words, computes their common
linear depth bound, and writes the synchronized rows. The input consists of
the local radix exponents together with an upper bound on them.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedLayers.ScheduleProgram

open IntegerMultiplication IntegerMultiplication.Code ShortFourier.AxisWord

/-- Common number of scheduled local steps used at the supplied maximum exponent. -/
def radixBudget (u : Tally) : Tally :=
  ((tally 18576).map fun _ => u).flatten ++ tally 27882

theorem radixBudget_poly : Poly radixBudget := by
  have h := ((Code.Poly.const (tally 18576)).pair (Code.Poly.identity (X := Tally))).compose
    (Packed.chamber (X := Tally))
  exact (h.compose Easy.flatten.poly).app (Code.Poly.const (tally 27882))

@[simp] theorem radixBudget_length (u : Tally) :
    (radixBudget u).length = 18 * (1032 * u.length + 1549) := by
  have h (x y : Tally) : (x.map (fun _ => y)).flatten.length = x.length * y.length := by
    simp [List.map_const', List.length_flatten]
  simp only [radixBudget, List.length_append, h, tally_length]
  omega

/-- Whole output word, with a single named slot type on each row. -/
def radixPlan (p : List Tally × Tally) : List (Row Inst) :=
  plan instructionKind ((p.1.map fixedWord), radixBudget p.2)

theorem radixPlan_poly : Poly radixPlan :=
  ((Easy.fst.poly.compose (Poly.maps _ fixedWord_poly)).pair
    (Easy.snd.poly.compose radixBudget_poly)).compose (plan_poly instructionKind_poly)

/-- Polynomial setup time and visited cells, including writing all of the output on tape. -/
theorem radixPlan_machine : PolyTreeMachine size send (fun p => send (radixPlan p)) :=
  polyTreeMachine_of_BT (radixPlan_poly.on (Dom.base _)) (Dom.base _)

theorem radixPlan_length (p : List Tally × Tally) :
    (radixPlan p).length = 54 * (1032 * p.2.length + 1549) := by
  simp [radixPlan, plan, cycle, List.length_flatMap, List.map_const', List.sum_replicate]
  omega

/-- At each block the finite machine's output executes exactly the restored fixed-bit word. -/
theorem radixPlan_executes {n : ℕ} (u : Fin n → Tally) (L : Tally) (hu : ∀ i, (u i).length ≤ L.length)
    (i : Fin n) :
    (radixPlan (List.ofFn u, L)).filterMap (fun r => readBlock r i.val) = fixedWord (u i) := by
  have h (i : Fin n) : (fixedWord (u i)).length ≤ (radixBudget L).length := by
    apply (fixedWord_length_le (u i)).trans
    rw [radixBudget_length]
    gcongr
    exact hu i
  unfold radixPlan
  rw [List.map_ofFn, ← recover_tally (radixBudget L)]
  exact plan_executes instructionKind (fun i => fixedWord (u i)) h i

end SynchronizedLayers.ScheduleProgram

end NearSquareRoot
end Computability
end OAI
