import OAI.Hierarchy.DescentTerminalOperandSlots

namespace OAI
/-! # Dense ordinals in the row-major operand rectangle -/
namespace Hierarchy.DescentSixParty.Reached
open DescentKernelHistory DescentLocalPrivateNames DescentTerminalChronologicalBooks DescentTerminalPointerIssue
open scoped Classical
noncomputable section
theorem earlier_count {Y : Type} [Fintype Y] {n : ℕ} (e:Y≃Fin n) (u:Y) :
    (Finset.univ.filter (fun v:Y=>(e v).val<(e u).val)).card=(e u).val :=by
  classical
  let xs:=Finset.univ.filter (fun v:Y=>(e v).val<(e u).val)
  change xs.card=(e u).val
  have mapped : xs.map e.toEmbedding=Finset.Iio (e u) := by
    ext t
    constructor
    · intro ht
      obtain ⟨v,hv,rfl⟩:=Finset.mem_map.mp ht
      exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hv).2
    · intro ht
      refine Finset.mem_map.mpr ⟨e.symm t,?_,e.apply_symm_apply t⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using Finset.mem_Iio.mp ht⟩
  calc
    xs.card=(xs.map e.toEmbedding).card := by rw [Finset.card_map]
    _=(e u).val := by rw [mapped,Fin.card_Iio]


theorem rectangle_slot_number {Tag V : Type} (r : Recipe Tag V)
    (number : r.Node≃Fin (Fintype.card r.Node)) {N A : ℕ}
    (nodes : Fintype.card r.Node≤N) (args : ∀u,r.arity u≤A) (s : Slot r) :
    (number s.1).val*A+s.2.val=
      (slot r (number.toEmbedding.trans Fin.valEmbedding) nodes args s).val :=by
  have ord : (ordinal (number.toEmbedding.trans Fin.valEmbedding) s.1).val=(number s.1).val:=by
    rw [ordinal_val]
    exact earlier_count number s.1
  simp [slot,row,finProdFinEquiv_apply_val,ord,Nat.mul_comm,Nat.add_comm]

end
end Hierarchy.DescentSixParty.Reached

end OAI
