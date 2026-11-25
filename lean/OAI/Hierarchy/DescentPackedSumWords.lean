import OAI.Hierarchy.DescentColonySplitRAM
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Packed lane values and sums of compiled row expressions -/
namespace Hierarchy.DescentPackedSumWords
open DescentSIMDLookup DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H G M w : ℕ}
theorem lanes_val {b : ℕ} (x : Fin H→Fin G→Cell b) (p : Row H G M) : (data x p).val=
    ∑j:Fin M,(if live:p.2.val*M+j.val<G then (x p.1 ⟨_,live⟩).val else 0)*(2^b)^j.val :=by
  change (finFunctionFinEquiv _).val=_;rw [finFunctionFinEquiv_apply];apply Finset.sum_congr rfl;intro i _
  by_cases yes:p.2.val*M+i.val<G <;> simp [yes]

theorem eval_sum {α : Type} (f : α→Expr) (a : α→ℕ) (m : Memory w) (r : Word w)
    (ok : ∀i,(f i).eval m r=(a i:Word w)) (xs : List α) :
    (total f xs).eval m r=((xs.map a).sum:Word w) :=by
  induction xs with
  | nil=>rfl
  | cons i is ih=>simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ok,ih]

end
end Hierarchy.DescentPackedSumWords

end OAI
