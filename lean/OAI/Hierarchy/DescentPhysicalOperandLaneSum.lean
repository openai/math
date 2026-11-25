import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! Native addition of the operand families, including the last partial word. -/
namespace Hierarchy.DescentResetOperandSetup
open DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H G M w b : ℕ}
abbrev Values (H G b : ℕ) :=Fin H→Fin G→Cell b

theorem sum_source (m : Memory w) (z l r : Values H G b) (left right : Expr)
    (sl : Source left l M m) (sr : Source right r M m)
    (total : ∀h g,(z h g).val=(l h g).val+(r h g).val) :
    Source (.op .add left right) z M m:=by
  intro p
  have digits (x : Fin M→Cell b) : (encode b M x).val=∑i,(x i).val*(2^b)^i.val:=
    finFunctionFinEquiv_apply x
  have sums : (data z p).val=(data l p).val+(data r p).val:=by
    simp only [data,digits,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases live:p.2.val*M+i.val<G
    · simp only [dite_eq_left live,total,add_mul]
    · simp [live]
  change left.eval m _+right.eval m _=_
  rw [sl p,sr p,←Nat.cast_add,sums]

/-- The selected owner may vary between adjacent lanes of one processor word. -/
theorem select_three (m : Memory w) (z l r t : Values H G b) (a c d : Expr)
    (sl : Source a l M m) (sr : Source c r M m) (st : Source d t M m)
    (owner : ∀h g,(z h g=l h g ∧ r h g=0 ∧ t h g=0) ∨
      (l h g=0 ∧ z h g=r h g ∧ t h g=0) ∨ (l h g=0 ∧ r h g=0 ∧ z h g=t h g)) :
    Source (.op .add a (.op .add c d)) z M m:=by
  let sum:=fun h g=>if r h g=0 then t h g else r h g
  have pair:=sum_source m sum r t c d sr st (by
    intro h g
    rcases owner h g with ⟨_,hr,ht⟩|⟨_,_,ht⟩|⟨_,hr,_⟩
    · simp [sum,hr,ht]
    · by_cases hr : r h g = 0 <;> simp [sum,hr,ht]
    · simp [sum,hr])
  exact sum_source m z l sum a _ sl pair (by
    intro h g
    rcases owner h g with ⟨hz,hr,ht⟩|⟨hl,hz,ht⟩|⟨hl,hr,hz⟩
    · simp [sum,hz,hr,ht]
    · by_cases hr : r h g = 0 <;> simp [sum,hz,hl,ht,hr]
    · simp [sum,hz,hl,hr])

end
end Hierarchy.DescentResetOperandSetup

end OAI
