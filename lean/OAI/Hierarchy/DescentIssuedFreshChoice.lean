import OAI.Hierarchy.DescentIssuedRoleChoice

namespace OAI
/-! # Positive public and private requests in the attained operand lookup -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentDenseHostOrder DescentResetOperandSetup DescentResetPublicOperandBook
open DescentResetRetainedSetup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "C" => a.successor.setup
local notation "R" => (C).retained
local notation "cfg" => publicOperands z roots menu.payload
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (i : Fin (publicOperands z roots menu.payload).mouths)
local notation "reg" => (cfg).reg x
local notation "loc" => (finProdFinEquiv.symm i : Fin (cfg).args × Fin (cfg).nodes)
local notation "prv" b:arg f:arg => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
  (loc).2.val (loc).1.val f (reg) : Cell b)
local notation "pub" b:arg f:arg => (cfg).column z.board b f i x
variable (hostEq : a.successor.setup.placement.oldHosts=a.successor.setup.retained.hosts) (groupEq : a.successor.setup.placement.groups*a.successor.setup.placement.blocks=a.successor.setup.retained.grouped)
variable (packet : a.successor.setup.seven.Packets) (strips : a.successor.setup.retained.Strips) (which : a.successor.setup.seven.control.Targets)
local notation "Y" => (C).assignedDigits hostEq groupEq which packet strips
variable (block : Fin a.successor.setup.placement.blocks) (arg : Fin a.successor.setup.retained.args) (node : Fin a.successor.setup.retained.nodes)
variable (host : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
local notation "o" t:arg f:arg => (R).outputID t f arg node
local notation "ret" t:arg f:arg => ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name (Y) (o t f) block host g).val : Cell (C).fieldBits)
variable (row : a.successor.setup.cable.Input) (head : a.successor.setup.cable.header row 0=((DescentRetainedTargetPlacement.Chart.compact a.successor.setup.placement a.successor.setup.seven.batch menu.keep name (a.successor.setup.assignedDigits hostEq groupEq which packet strips) (a.successor.setup.retained.outputID 0 0 arg node) block host g).val : Cell a.successor.setup.fieldBits))
variable (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → (((publicOperands z roots menu.payload).reg x) 1).val=0)
variable (physical : ∀hv : host.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
    (((publicOperands z roots menu.payload).reg x) 3).val=(a.successor.setup.placement.shape (name ⟨host.val,hv⟩)).val)
local notation "q" => (C).cable.query row
local notation "p" => prv (C).queryBits 0
local notation "s" => pub (C).queryBits none

local notation "charge" f:arg => (C).cable.priceField f row
local notation "rotorValue" f:arg => prv (C).fieldBits (f).succ
local notation "publicValue" f:arg => pub (C).fieldBits (some f)
local notation "posted" f:arg => (((ret 1 f).val+(charge f).val+(rotorValue f).val+(publicValue f).val:ℕ) : Cell (C).fieldBits)

include head in
theorem fresh_carried_off
    (away : ∀hv : host.val<U,menu.keep ((C).placement.shape (name ⟨host.val,hv⟩))≠true) :
    q=0 ∧ ∀f,ret 1 f=0 ∧ charge f=0 :=by
  have emptyCell : ∀ t d,ret t d=0:=by
    intro t d
    by_cases hv : host.val<U
    · have dead : menu.keep ((C).placement.shape (name ⟨host.val,hv⟩))≠true:=fun keep=>away hv keep
      simp [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,hv,
        DescentRetainedTargetPlacement.Chart.selected,dead]
    · simp [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,hv]
  have absent : (C).cable.found row=none:=(C).cable.absent row (by rw [head,emptyCell];exact Nat.zero_ne_one)
  have qzero : q=0:=(C).cable.query_none row absent
  have d0 := (C).cable.charge_none row absent
  have czero (f : Fin 7) : charge f=0:=by
    by_cases t : f=2
    · simp [DescentResetRetainedCableLaw.Shape.priceField,t,d0]
    · by_cases u : f=3 <;> simp [DescentResetRetainedCableLaw.Shape.priceField,t,u,d0]
  exact ⟨qzero,fun f=>⟨emptyCell 1 f,czero f⟩⟩

include head blank physical in
theorem issued_fresh_public {out : ℕ×ℕ×ℕ×Bool}
    (hit : (cfg).mixed z.board (loc).2.val (loc).1.val x=some out)
    (present : s≠0) :
    queryDigit (a:=a) q p s=s ∧ ∀f,posted f=publicValue f :=by
  have away (hv : host.val<U) : menu.keep ((C).placement.shape (name ⟨host.val,hv⟩))≠true:=by
    intro keep
    exact present (menu.private_public_off name host x i (C).queryBits none 0 blank physical hv keep).2
  obtain ⟨_,other⟩:=menu.fresh_carried_off name hostEq groupEq packet strips which block arg node host g row head away
  have inactive:=(cfg).mixed_excludes_private z.board (loc).2.val (loc).1.val (cfg).split x out hit
  have chosen : queryDigit (a:=a) q p s=s :=by
    rcases menu.query_owner name x i hostEq groupEq packet strips which block arg node host g row head blank physical with h|h|h
    · exact (present h.2.2).elim
    · exact (present h.2.2).elim
    · exact h.2.2
  refine ⟨chosen,fun f=>?_⟩
  obtain ⟨previous,delta⟩:=other f
  simp [previous,delta,inactive f.succ]

include head blank physical in
theorem issued_fresh_rotor (present : p≠0) :
    queryDigit (a:=a) q p s=p ∧ ∀f,posted f=rotorValue f :=by
  have away (hv : host.val<U) : menu.keep ((C).placement.shape (name ⟨host.val,hv⟩))≠true:=by
    intro keep
    exact present (menu.private_public_off name host x i (C).queryBits none 0 blank physical hv keep).1
  obtain ⟨_,other⟩:=menu.fresh_carried_off name hostEq groupEq packet strips which block arg node host g row head away
  have empty : (cfg).mixed z.board (loc).2.val (loc).1.val x=none:=by
    cases hit : (cfg).mixed z.board (loc).2.val (loc).1.val x with
    | none=>rfl
    | some out=>
      have off:=(cfg).mixed_excludes_private z.board (loc).2.val (loc).1.val (cfg).split x out hit
      exact (present (by simp [off 0])).elim
  have chosen : queryDigit (a:=a) q p s=p :=by
    rcases menu.query_owner name x i hostEq groupEq packet strips which block arg node host g row head blank physical with h|h|h
    · exact (present h.2.1).elim
    · exact h.2.1
    · exact (present h.2.1).elim
  refine ⟨chosen,fun f=>?_⟩
  obtain ⟨previous,delta⟩:=other f
  have inactive : publicValue f=0:=by simp [DescentResetPublicOperandBook.Config.column,empty]
  simp only [previous,delta,inactive,Fin.val_zero,Nat.zero_add,Nat.add_zero]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (rotorValue f).isLt

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
