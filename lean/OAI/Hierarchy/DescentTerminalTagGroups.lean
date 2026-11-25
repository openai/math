import OAI.Hierarchy.DescentTerminalTagPacking
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # Batching a finite family of local tagged calls -/

namespace Hierarchy.Tagged.TerminalGroups
open ThreeFlat.Routing
open scoped BigOperators Classical

private def assign (n s w L : ℕ) (b : Fin (poolBatchCount L (2^s)))
    (p : Row s × Fin (pins n w)) : (Fin L × Fin (pins n w)) ⊕ Bool :=
  TerminalPack.prefixPin n w L (finProdFinEquiv (b,p.1),p.2)

/-- Number the local calls consecutively across all batches and pin the final
unused slots to the identity input. -/
def wire (n s w L : ℕ) (hw : w ≤ n+s) (b : Fin (poolBatchCount L (2^s))) :
    Fin (pins (n+s) (n+s)) → (Fin L × Fin (pins n w)) ⊕ Bool :=
  Sum.elim (assign n s w L b) Sum.inr ∘ TerminalPack.wire n s w hw

theorem eval (F : Type*) [CommMonoidWithZero F] (n s w L : ℕ) (hw : w ≤ n+s)
    (x : Fin L × Fin (pins n w) → Bool) :
    (∏ b : Fin (poolBatchCount L (2^s)),
      coeff F (n+s) (n+s) (Sum.elim x id ∘ wire n s w L hw b)) =
      ∏ i : Fin L, coeff F n w (fun j => x (i,j)) := by
  let batches := poolBatchCount L (2^s)
  let factor := fun (i : Fin (batches*2^s)) =>
    coeff F n w (fun j => Sum.elim x id (TerminalPack.prefixPin n w L (i,j)))
  have piece (b : Fin batches) : coeff F (n+s) (n+s) (Sum.elim x id ∘ wire n s w L hw b) =
      ∏ a : Row s, factor (finProdFinEquiv (b,a)) := by
    have eqn : Sum.elim x id ∘ wire n s w L hw b =
        Sum.elim (Sum.elim x id ∘ assign n s w L b) id ∘ TerminalPack.wire n s w hw := by
      funext j
      cases hj : TerminalPack.wire n s w hw j <;> simp [wire,Function.comp_def,hj]
    exact (congrArg (coeff F (n+s) (n+s)) eqn).trans
      (TerminalPack.full_eval F n s w hw (Sum.elim x id ∘ assign n s w L b))
  simp_rw [piece]
  calc
    _ = ∏ i, factor i := by
      exact (Fintype.prod_prod_type (fun z : Fin batches × Row s=>factor (finProdFinEquiv z))).symm.trans
        (finProdFinEquiv.prod_comp factor)
    _ = _ := TerminalPack.prefix_eval F n w L (batches*2^s) (by
      simpa only [batches,Nat.mul_comm] using
        CallPool.count_le_batches_mul L (2^s) (Nat.two_pow_pos _)) x

/-- Rounding to a whole number of batches adds at most one full tag width. -/
theorem height_slots (n s L : ℕ) :
    poolBatchCount L (2^s)*2^(n+s) ≤ L*2^n+2^(n+s) := by
  have grouped : poolBatchCount L (2^s)*2^s ≤ L+2^s :=
    (Nat.div_mul_le_self (L+2^s-1) (2^s)).trans (Nat.sub_le ..)
  have scaled := Nat.mul_le_mul_right (2^n) grouped
  rw [pow_add]
  nlinarith only [scaled]

end Hierarchy.Tagged.TerminalGroups

end OAI
