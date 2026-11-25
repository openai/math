import OAI.Computability.BorderVNP.CrossingKernelAssembly
import OAI.Computability.BorderVNP.CrossingWordFrame

/-!
# The signed Boolean verifier for each integral mode entry

The packed normally ordered word circuits, the signed scalar circuit and the bounded
occupation-state guesses together give the path descriptions required by Lemma 4.1.
The hidden variables are numbered as one Boolean word. Size and witness bounds hold for
every pair of mode cutoff and source weight, independently of the coefficient field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.KernelFrame

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open Lemmata.FockCircuits.CrossingCircuit
open VPVNP.VerifierNetwork (Frame)
open CoefficientFrame (Query value query)
open scoped BigOperators

/-- Actual local verifier, with one numbered Boolean witness bank. -/
noncomputable def gates (marked : Bool) (L W : ℕ) : Frame (Query L W ⊕ Fin (width marked L W)) Bool :=
  (assemble marked W (WordFrame.frame true L) (WordFrame.frame false L)).subst
    (Frame.initial (Sum.map id (Fintype.equivFin (Hidden marked L W))))

/-- Lemma 4.1's signed path counts for the marked and bare modes, realized by Boolean circuits. -/
theorem gates_sum {L W : ℕ} (marked : Bool) (r : Fin W) (A I J : Index L) :
    ∑ y : Fin (width marked L W) → Bool, value ((gates marked L W).eval (Sum.elim (query r A I J) y)) =
      if marked then markedMode ℤ L W r (dualState ℤ L A.val) I J
      else oppositeMode ℤ L W r (dualSign A.val • Pi.single A 1) I J := by
  let e : Hidden marked L W ≃ Fin (width marked L W) := Fintype.equivFin _
  let reindex := e.arrowCongr (Equiv.refl Bool)
  refine (reindex.sum_comp (fun y => value ((gates marked L W).eval (Sum.elim (query r A I J) y)))).symm.trans ?_
  refine Eq.trans (Finset.sum_congr rfl (fun y _ => ?_))
    (assemble_sum marked (WordFrame.frame true L) (WordFrame.frame false L) (WordFrame.frame_sum true) (WordFrame.frame_sum false) r A I J)
  apply congrArg value
  funext out
  rw [gates, Frame.subst_eval]
  congr 1
  funext j
  rw [Frame.initial_eval]
  cases j with
  | inl j => rfl
  | inr j => exact congrArg y (e.symm_apply_apply j)

/-- Polynomial number of shared Boolean gates, including all signs and binary multiplicities. -/
theorem gates_size (marked : Bool) (L W : ℕ) : (gates marked L W).size ≤ (L+W+2)^100 := by
  rw [gates, Frame.subst_size, Frame.initial_size, Nat.zero_add]
  exact assemble_size marked _ _ (WordFrame.frame_size true L) (WordFrame.frame_size false L)

end Crossing.Signed.KernelFrame

end BorderVNP
end Computability
end OAI
