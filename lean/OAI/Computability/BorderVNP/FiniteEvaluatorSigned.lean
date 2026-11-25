import OAI.Computability.BorderVNP.FiniteEvaluatorStatic
import OAI.Computability.BorderVNP.FiniteScalarLibraryCalls

/-! # Signed private validation inside the combined finite-field library -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM TeamRAM TeamSite TeamPrivateFragment TeamPrivateTape TeamPrivateValue FieldProcessor
open FiniteScalarLibrary

variable {w m g a : ℕ} {Q Γ : Type} {F : Type*} [Field F]

/-- Give an existing signed routine its native signed field scalar at every actual
successful terminal. Its signed zero event corresponds to a rejecting private halt. -/
def signedReturn : FieldSelect.Return Q Γ F m := fun _ _ b => signed b 1

private theorem trackSigned {d : ℕ} (T : Table Q d) (f : ℕ) (q : Q) (ts : Fin d → Track) (bs : List Bool) :
    (trackReturn T (fun _ _ b => signed b (1:F)) f q ts bs).getD 0 =
      ((TeamPrivateCall.evaluate T f q ts bs).map (fun x => ((TeamPrivateCall.sign x.1).value : F))).getD 0 := by
  induction f generalizing q ts bs with
  | zero => rfl
  | succ f ih =>
    cases h : T q (heads ts) with
    | halt ok neg => cases bs <;> cases ok <;> cases neg <;> simp [trackReturn,TeamPrivateCall.evaluate,h,signed,TeamPrivateCall.sign,Sign.value]
    | one => simpa only [trackReturn,TeamPrivateCall.evaluate,h] using ih _ _ _
    | two =>
      cases bs with
      | nil => simp [trackReturn,TeamPrivateCall.evaluate,h]
      | cons b bs => simpa only [trackReturn,TeamPrivateCall.evaluate,h] using ih _ _ _

/-- Every genuine signed private event, including an absorbed zero, has the same
weight when the terminal scalar is interpreted in the finite-field evaluator. -/
theorem signed_return (M : TeamSite.Macro Q Γ m g) (fuel : ℕ) (e : TeamRAM.Event w)
    (h : M.eval fuel e.old e.choices = some e.sign) :
    (returned M (signedReturn (F := F)) fuel e).getD 0 = (e.sign.value : F) := by
  unfold returned
  rw [← trackReturn_eq]
  change (trackReturn (trackTable M.alphabet M.table) (fun _ _ b => signed b (1:F)) fuel M.start (M.initial e.old) e.choices).getD 0 = _
  rw [trackSigned]
  have applied := congrArg (fun x : Option Sign => (x.map (fun z => (z.value:F))).getD 0) h
  simpa only [TeamSite.Macro.eval,Option.map_map,Function.comp_def,Option.map_some,Option.getD_some] using applied

/-- Every original private identifier remains a true signed weight in the combined
library on its fetched finite-field trajectory. -/
theorem combined_signed [Fintype F] (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth)
    (fuel : ℕ) (j : Fin 8) (hj : j≠1) (e : TeamRAM.Event w) (h : (combine F lib j).eval fuel e.old e.choices = some e.sign) :
    (returned (combine F lib j) (returns F lib (fun _ => signedReturn) j) fuel e).getD 0 = (e.sign.value:F) := by
  rw [original_return F lib _ j hj]
  rw [original_eval F lib j hj] at h
  exact signed_return (lib j) fuel e h

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
