import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-! # Summing the traces of repeated evaluator transitions -/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorScheduleEffects

variable {S I : Type*} [Fintype I]

/-- Sum the continuation over the choices of one linear step. -/
def stepEffect (next : Option ℕ → S → I → S) (a : Option ℕ) (f : S → ℕ) (s : S) : ℕ :=
  ∑ o : I, f (next a s o)

/-- Sum over the choice traces of all repetitions of the same linear step. -/
def repeatEffect (next : Option ℕ → S → I → S) (a : Option ℕ) (d : ℕ) (f : S → ℕ) (s : S) : ℕ :=
  ∑ z : Fin d → I, f ((List.ofFn z).foldl (next a) s)

/-- Folding the step effects in chronological order counts each trace once. -/
theorem repeatEffect_eq_foldr (next : Option ℕ → S → I → S) (a : Option ℕ) (d : ℕ)
    (f : S → ℕ) (s : S) :
    repeatEffect next a d f s = (List.replicate d a).foldr (stepEffect next) f s := by
  induction d generalizing s with
  | zero => simp [repeatEffect]
  | succ d ih =>
    let wt (z : Fin (d+1) → I) := f ((List.ofFn z).foldl (next a) s)
    change (∑ z, wt z) = _
    rw [← (Fin.consEquiv (fun _ : Fin (d+1) => I)).sum_comp wt, Fintype.sum_prod_type,
      List.replicate_succ, List.foldr_cons]
    apply Finset.sum_congr rfl
    intro o _
    simpa only [wt, repeatEffect, Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.foldl_cons] using ih (next a s o)

end EvaluatorScheduleEffects

end VPVNP
end Computability
end OAI
