import OAI.Computability.BorderVNP.FiniteEvaluatorRouteScheduleOwners

/-! # Original finite cell and delivery numbers in the public histogram -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Crossing Physical MeanChoice LabelIndex RoutingISA

variable {l : Layout} {dir : LabelIndex.Layout} {before m : ℕ → ℕ} {ep : Endpoints dir before}
    {D n blocks b K h : ℕ} {P : Type*} {bits : P → ℕ} {A : Type*} [Fintype A]
    (N : Network D P bits) (cell : N.Site → Fin l.cells) (recv : A → Fin l.cells) (width : A → ℕ)
    (same : l.cells=dir.cells) {edgeOrd : N.CrossingEdge cell ↪ Fin dir.cableCount}
    {dataOrd : A ↪ Fin dir.deliveryCount}
    (placed : RowPlacement (networkRows N cell recv width) (fromTables dir before ep)
      (finCongr same) (edgeOrd.sumMap dataOrd))

private theorem finRange_cast {x y : ℕ} (e : x=y) :
    (List.finRange y).map (finCongr e).symm = List.finRange x := by
  subst y
  exact List.map_id _

include placed in
/-- Reading the emitted fixed-order rows recovers exactly the source operands'
widths at each original numeric cell and its ascending conditional-mean label.
Slots in the native allocated directory which carry zero bits contribute zero. -/
theorem numbered_directory_image (pos : 0<l.groups) (decl : LengthDeclaration n l.groups)
    (native : PhysicalImage l m blocks b K h decl (directoryLabel same pos ep n)
      (directoryRecv same ep) (fun j => (deliveryAt dir before j.val).2)) :
    PhysicalImage l m blocks b K h decl
      (meanPackedLabel N cell recv width (List.finRange l.cells) n l.groups pos) recv width := by
  refine ⟨native.axes,native.axis,native.rows,native.selectors,native.alphabet,native.blockCount,
    native.blockWidth,?_,?_⟩
  · intro c
    have code := decoded_tableCodes N cell recv width dir before ep (finCongr same) placed n l.groups pos c
    rw [finRange_cast same] at code
    exact (native.labels c).trans (congrArg (fun value => (finFunctionFinEquiv value).val) code)
  · intro c
    rw [native.demands c]
    symm
    apply Fintype.sum_of_injective dataOrd dataOrd.injective
    · intro j unused
      have empty := placed.unused (.inr j) (by
        rintro ⟨i|a,eq⟩
        · contradiction
        · exact unused ⟨a,Sum.inr.inj eq⟩)
      change (deliveryAt dir before j.val).2=0 at empty
      simp [empty]
    · intro a
      have correct := placed.live (.inr a)
      change rowEquivalent
        (.delivery ⟨(deliveryAt dir before (dataOrd a).val).1,_⟩ (deliveryAt dir before (dataOrd a).val).2)
        (.delivery ((finCongr same) (recv a)) (width a)) at correct
      rcases correct with eq | ⟨empty,zero⟩
      · obtain ⟨dest,size⟩ := Traffic.delivery.inj eq
        have index : directoryRecv same ep (dataOrd a) = recv a := Fin.ext (congrArg (fun j : Fin dir.cells => j.val) dest)
        rw [index,size]
      · change (deliveryAt dir before (dataOrd a).val).2=0 at empty
        change width a=0 at zero
        simp only [empty,zero,ite_self]

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
