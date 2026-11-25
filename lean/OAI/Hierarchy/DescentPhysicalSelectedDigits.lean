import OAI.Hierarchy.DescentResetCarriedOwner

namespace OAI
/-! Packed arithmetic of the real carried, rotor, and surface operand columns. -/
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

def queryDigit (retained privateDigit publicDigit : Cell a.successor.setup.queryBits) :=
  if retained≠0 then retained else if privateDigit≠0 then privateDigit else publicDigit

private theorem queryDigit_of_retained (u v t : Cell a.successor.setup.queryBits) (nonzero : u ≠ 0) :
    queryDigit (a:=a) u v t = u := ite_eq_left nonzero
private theorem queryDigit_of_private (u v t : Cell a.successor.setup.queryBits) (absent : u = 0) (nonzero : v ≠ 0) :
    queryDigit (a:=a) u v t = v := by
  unfold queryDigit
  exact (ite_eq_right (not_not_intro absent)).trans (ite_eq_left nonzero)
private theorem queryDigit_of_public (u v t : Cell a.successor.setup.queryBits) (absent : u = 0) (internal : v = 0) :
    queryDigit (a:=a) u v t = t := by
  unfold queryDigit
  exact (ite_eq_right (not_not_intro absent)).trans (ite_eq_right (not_not_intro internal))

include head blank physical in
theorem query_owner :
    (queryDigit (a:=a) q p s=q ∧ p=0 ∧ s=0) ∨
    (q=0 ∧ queryDigit (a:=a) q p s=p ∧ s=0) ∨
    (q=0 ∧ p=0 ∧ queryDigit (a:=a) q p s=s) :=by
  by_cases live:q=0
  · by_cases private_:p=0
    · exact Or.inr (Or.inr ⟨live,private_,queryDigit_of_public (a:=a) q p s live private_⟩)
    have raw:=(cfg).disjoint_at z.board (C).queryBits none i x 0 (cfg).split
    rcases raw with hs | hp
    · exact Or.inr (Or.inl ⟨live,queryDigit_of_private (a:=a) q p s live private_,hs⟩)
    · exact (private_ (by simp only [hp,Nat.cast_zero])).elim
  have tagged:((C).cable.header row 0).val=1:=by
    by_contra no
    exact live ((C).cable.query_none row ((C).cable.absent row no))
  rw [head] at tagged
  obtain ⟨hp,hs⟩:=menu.carried_gate name host x i (C).queryBits none 0 blank physical
    (Y) (o 0 0) block g tagged
  exact Or.inl ⟨queryDigit_of_retained (a:=a) q p s live,hp,hs⟩

variable (f : Fin 7) (bits : 2<2^a.successor.setup.fieldBits)
local notation "d" => (C).cable.priceField f row
local notation "p_" => prv (C).fieldBits f.succ
local notation "s_" => pub (C).fieldBits (some f)

include head blank physical bits in
theorem posted_field_room :
    (ret 1 f).val+(d).val+(p_).val+(s_).val<2^(C).fieldBits:=by
  by_cases off:d=0
  · simpa only [off,Fin.val_zero,Nat.add_zero] using
      menu.span_room name (Y) (o 1 f) block host g x i f blank physical
  have choice:f=2 ∨ f=3:=by
    by_contra nope
    push Not at nope
    exact off (by simp [DescentResetRetainedCableLaw.Shape.priceField,nope.1,nope.2])
  have tag:((C).cable.header row 0).val=1:=by
    by_contra no
    have empty_:=(C).cable.absent row no
    have zero_:=(C).cable.charge_none row empty_
    exact off (by rcases choice with eq|eq <;>subst f <;> simp [DescentResetRetainedCableLaw.Shape.priceField,zero_])
  rw [head] at tag
  have old:=(C).assigned_cable_zero hostEq groupEq which packet strips menu.keep name block arg node host g f
    (by rcases choice with h|h <;>rw [h] <;> decide) bits tag
  obtain ⟨hp,hs⟩:=menu.carried_gate name host x i (C).fieldBits (some f) f.succ blank physical
    (Y) (o 0 0) block g tag
  simp only [old,hp,hs,Fin.val_zero,Nat.zero_add,Nat.add_zero]
  exact (d).isLt

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
