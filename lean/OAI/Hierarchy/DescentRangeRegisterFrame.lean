import OAI.Hierarchy.DescentRangeRegisterCore

namespace OAI
/-! Equality of retained argument words on their physical banks suffices for equality of the decoded register. -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentKernelHistory DescentOperandStateBanks
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentDatedAddressBook
open DescentDatedPriorOperand ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section

theorem fromRAM_frame {F P : Type} [Field F] {d w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W} (a : PriorResetArchive) (l : Layout) (width : ℕ)
    (m before : Memory w) (pos : 0<l.lanes) (block : NodeOrder.All B→Fin l.blocks)
    (host : NodeOrder.All B→Fin l.hosts) (groupOf : NodeOrder.All B→Fin l.groups)
    (number : NodeOrder.All B→Fin l.nodes)
    (same : ∀x p (r : Fin l.rows), m ((previousBank l a.arguments x p).base+r.val)=
      before ((previousBank l a.arguments x p).base+r.val)) :
    fromRAM a l width m pos block host groupOf number=
      fromRAM a l width before pos block host groupOf number := by
  let one := fromRAM a l width m pos block host groupOf number
  let two := fromRAM a l width before pos block host groupOf number
  have packed : one.packed=two.packed := by
    funext x i f
    by_cases live : i<l.operands
    · let page_ := DescentOperandStateBanks.page (page f) (⟨i,live⟩ : Fin l.operands)
      have kept (chunk : Fin (chunks l.groups l.lanes)) :
          m ((previousBank l a.arguments (block x) page_).base +
            (row l.hosts l.groups l.lanes (host x,chunk)).val) =
          before ((previousBank l a.arguments (block x) page_).base +
            (row l.hosts l.groups l.lanes (host x,chunk)).val) :=
        same (block x) page_ (row l.hosts l.groups l.lanes (host x,chunk))
      simp only [one,two,fromRAM,dite_eq_left live]
      rw [kept]
    · simp only [one,two,fromRAM,dite_eq_right live]
  exact congrArg (fun g => (⟨width,l.nodes,g,number⟩ : Register B)) packed


/-- A registered change of coordinates and physical frame can be applied in the same step. -/
theorem fromRAM_layout_frame {F P : Type} [Field F] {d w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W} (a : PriorResetArchive) (l l' : Layout) (eqL : l=l') (width : ℕ)
    (m before : Memory w) (pos : 0<l.lanes) (block : NodeOrder.All B→Fin l.blocks)
    (host : NodeOrder.All B→Fin l.hosts) (groupOf : NodeOrder.All B→Fin l.groups)
    (number : NodeOrder.All B→Fin l.nodes)
    (same : ∀x p (r : Fin l'.rows), m ((previousBank l' a.arguments x p).base+r.val)=
      before ((previousBank l' a.arguments x p).base+r.val)) :
    fromRAM a l width m pos block host groupOf number=
      fromRAM a l' width before (by simpa only [←eqL] using pos)
        (fun x=>(block x).cast (congrArg Layout.blocks eqL)) (fun x=>(host x).cast (congrArg Layout.hosts eqL))
        (fun x=>(groupOf x).cast (congrArg Layout.groups eqL)) (fun x=>(number x).cast (congrArg Layout.nodes eqL)) := by
  cases eqL
  exact fromRAM_frame a l width m before pos block host groupOf number same

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
