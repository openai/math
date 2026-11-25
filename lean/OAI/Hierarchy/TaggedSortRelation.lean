import OAI.Hierarchy.TaggedSortShell

namespace OAI
/-! # Evaluation of the two-terminal stable tagged sort -/

namespace Hierarchy.Tagged.SortRelation

open ThreeFlat Routing SortNetwork Tagged.Radix
open scoped BigOperators Classical
noncomputable section

/-- Pointwise two-terminal evaluation, including the full output comparison. -/
theorem eval (F : Type*) [CommSemiring F] {h w d : ℕ} (digit : Fin d → Fin w)
    (input : Records h w) (y : Data h w → Bool) :
    (∑ hole : Fin (pins h (h+w)) → Bool,
      TypedWiring.value (shell F digit) (Sum.elim (Sum.elim (pack input) y) hole) * coeff F h (h+w) hole) =
    if y = pack (input ∘ Tuple.sort (fun i => addressEquiv d (input i ∘ digit))) then 1 else 0 := by
  let dense := TableCompiler.localTableNetwork (coeff F h (h+w))
  let T := TableCompiler.localTableNetwork fun v : Data h w → Bool => if v = y then (1:F) else 0
  have exactN (x) : dense.eval x = coeff F h (h+w) x := TableCompiler.localTableNetwork_eval _ _
  have test (v : Data h w → Bool) : T.eval v = if v = y then 1 else 0 := TableCompiler.localTableNetwork_eval _ _
  have rhs := stable_digit_eval digit dense exactN T input
  rw [test] at rhs
  let result := pack (input ∘ Tuple.sort (fun i => addressEquiv d (input i ∘ digit)))
  have order : (if y=result then (1:F) else 0) = (if result=y then 1 else 0) := by
    by_cases e : y = result
    · rw [ite_eq_left e,ite_eq_left e.symm]
    · rw [ite_eq_right e,ite_eq_right (Ne.symm e)]
  rw [order, ← rhs, shell, OracleCut.contract, sortThen, BitNetwork.glue_eval]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fintype.prod_sum_type, Fintype.prod_option, modules, siteWire,
    TableCompiler.localTableNetwork_eval, Fin.val_zero, ite_true, Fin.val_one, Nat.one_ne_zero,
    ite_false, BitSource.read, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inr, Fintype.prod_boole, ← funext_iff]
  change (_ * (if _ = y then 1 else 0)) * coeff F h (h+w) _ =
    (switchOfTag dense).eval _ * (T.eval _ * _)
  rw [test, switchOfTag, BitNetwork.restrictPins_eval, exactN]
  simp only [switchIndex, Option.map_some, Option.getD_some, Function.comp_apply]
  have projected (s : BitSource (Fintype.card (Hidden h w)) (Fintype.card (Payload h w))) :=
    lift_read (h := h) (w := w) s a (pack input) y
  simp only [BitSource.read, Function.comp_apply] at projected
  simp_rw [projected]
  by_cases ok : (fun j : Data h w => (wires digit (some none) j).read a (pack input)) = y
  · simp only [BitSource.read] at ok
    simp only [ite_eq_left ok, mul_one, one_mul]
    apply Eq.trans (mul_comm _ _)
    first | rfl
  · simp only [BitSource.read] at ok
    simp only [ite_eq_right ok, mul_zero, zero_mul]

end
end Hierarchy.Tagged.SortRelation

end OAI
