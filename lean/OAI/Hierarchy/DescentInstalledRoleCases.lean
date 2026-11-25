import OAI.Hierarchy.DescentResetTapArity
import OAI.Hierarchy.DescentBatchedNodeOrder

namespace OAI
/-! # Original action, arity and root order of each physically installed reset gate -/
namespace Hierarchy.DescentBatchedBank
open Computability.BorderVNP.Crossing DescentRotor DescentKernelHistory DescentResetGates DescentMixedRouter
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (u m p : ℕ) (hp : 0<p) (fit : u=m*p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ)
variable (select : ∀s w,Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network G hw u contact input site owner align select D
local notation "coeff" => DescentMixedRouter.Ordered.coefficients G hw u contact input site owner align key D select


local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
local notation "dev" => DescentMixedRouter.device G hw u contact input site owner align (D:=D)

open DescentLaneGates DescentPackedResetRotorRoles
/-- Index and opcode are observed quantities on the combined bank. -/
def InstalledRole (s : Bool) (w : W) : (c : Ch s w)→(dev c).Site→ℕ→ℕ→CanonicalTag (2^n)→Prop
  | .exceptional _,_,_,arity,tag=>role tag=5 ∧ arity=2
  | .good _ _ _ P,⟨v,.inl false⟩,slot,_,tag=>∃r : Fin P.layers,∃j : Fin m,
      slot=m*r.val+j.val ∧ tag=.inl (P.rotation r,v)
  | .good _ _ _ _,⟨_,.inl true⟩,_,_,_=>False
  | .good _ _ _ _,⟨_,.inr _⟩,_,arity,tag=>(role tag=if arity=2 then 5 else 3) ∧ (arity=1 ∨ arity=2)

local notation "prog" => sizedProgram G hw u m p hp fit contact input site owner align key D select
local notation "ord" => DescentBatchedNodeOrder.sizedOrder G hw m p hp contact input site owner align key D u fit select
local notation "spec" => InstalledRole G hw u m contact input site owner align D

omit [Fintype R] in
private theorem device_roles (side : Bool) (root : W)
    (c : Choice (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align side root)
    (cell : (DescentMixedRouter.device G hw (m*p) contact input site owner align (D:=D) c).Site)
    (z : (deviceProgram G hw m p hp contact input site owner align key D c cell).Node) :
    InstalledRole G hw (m*p) m contact input site owner align D side root c cell
      ((DescentBatchedNodeOrder.deviceOrder G hw m p hp contact input site owner align key D c cell z).val)
      (((deviceProgram G hw m p hp contact input site owner align key D c cell).op z).arity)
      (((deviceProgram G hw m p hp contact input site owner align key D c cell).op z).tag) := by
  cases c with
  | exceptional data=>exact ⟨rfl,rfl⟩
  | good first last pay circuit=>
    rcases cell with ⟨v,(_|_)|i⟩
    · rcases z with ⟨r,j⟩
      exact ⟨r,j,DescentBatchedNodeOrder.root_number G hw m p hp contact input site owner align key D first last pay circuit v r j,rfl⟩
    · exact z.elim
    · exact ⟨DescentResetTapEmission.tap_role D m p hp contact input site owner align side root G first last circuit key v i z,
        DescentResetTapEmission.real_tap_arity D m p hp contact input site owner align side root G first last circuit key v i z⟩

omit [Fintype R] in
theorem sized_roles (v : (bank).Site) (z : (prog v).Node) :
    spec v.1.1 v.1.2 (select v.1.1 v.1.2) v.2 ((ord v z).val) (((prog v).op z).arity) (((prog v).op z).tag):=by
  subst u
  rcases v with ⟨⟨side,root⟩,cell⟩
  exact device_roles G hw m p hp contact input site owner align key D side root (select side root) cell z

end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentRotor DescentKernelHistory DescentResetGates DescentChosenRouter DescentPackedResetRotorRoles
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "R" => Z.placement
local notation "chosen" => selected R Z.graph Z.positive Z.pay Z.circuit
local notation "program" => Z.laneProgram key m p hp fit
local notation "bitsAt" => Z.laneRecipe key m p hp fit
local notation "order" => Z.laneNodeOrder key m p hp fit
local notation "spec" => DescentBatchedBank.InstalledRole Z.graph Z.positive Z.unit m (R).contact (R).input (R).site (R).owner (R).align d

theorem bank_role_cases (v : Z.bank.Site) (z : (bitsAt v).Node) :
    spec v.1.1 v.1.2 (chosen v.1.1 v.1.2) v.2 ((order v z).val)
      (((program v).op z).arity) ((bitsAt v).tag z):=
  DescentBatchedBank.sized_roles Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen v z

theorem fallback_role (s : Bool) (t : Z.Fallback) (cell) (z : (bitsAt ⟨(s,.inr t),cell⟩).Node) :
    role ((bitsAt ⟨(s,.inr t),cell⟩).tag z)=5 ∧ ((program ⟨(s,.inr t),cell⟩).op z).arity=2:=
  Z.bank_role_cases key m p hp fit ⟨(s,.inr t),cell⟩ z

open private DescentChosenRouter.transportCircuit from OAI.Hierarchy.DescentInstalledNames

theorem good_root_role (s : Bool) (g : (R).Good) (v : Fin (2^Z.n))
    (z : (bitsAt ⟨(s,.inl g),⟨v,.inl false⟩⟩).Node) :
    ∃r : Fin (Z.circuit s g).layers,∃j : Fin m,
      (order ⟨(s,.inl g),⟨v,.inl false⟩⟩ z).val=m*r.val+j.val ∧
      (bitsAt ⟨(s,.inl g),⟨v,.inl false⟩⟩).tag z=.inl ((Z.circuit s g).rotation r,v) := by
  let facts {E : Type} (enum : Fintype E) {src dst : E → Fin (2^Z.n)}
      (chip : @BaseCircuit E enum Z.n h F _ Z.graph C Z.width Z.unit Z.positive src dst Z.pay)
      (slot : ℕ) (tag : CanonicalTag (2^Z.n)) : Prop :=
    ∃ r : Fin (@BaseCircuit.layers E enum Z.n h F _ Z.graph C Z.width Z.unit Z.positive src dst Z.pay chip),
      ∃ j : Fin m, slot = m*r.val+j.val ∧
        tag = .inl (@BaseCircuit.rotation E enum Z.n h F _ Z.graph C Z.width Z.unit Z.positive src dst Z.pay chip r, v)
  have pull {E : Type} {a b : Fintype E} {src dst : E → Fin (2^Z.n)}
      (chip : @BaseCircuit E a Z.n h F _ Z.graph C Z.width Z.unit Z.positive src dst Z.pay)
      (slot : ℕ) (tag : CanonicalTag (2^Z.n)) :
      facts b (DescentChosenRouter.transportCircuit (a := a) (b := b)
        (G := Z.graph) (hw := Z.positive) (pay := Z.pay) chip) slot tag →
        facts a chip slot tag := by
    cases Subsingleton.elim a b
    exact fun proof => proof
  let itemEnum : Fintype (Cells (R) s g) :=
    @Subtype.fintype A.graph.Edge (fun e => (R).owner s ((R).contact e) = Sum.inl g)
      (fun _ => Classical.propDecidable _) A.graph.finiteEdge
  exact pull (b := itemEnum) (Z.circuit s g)
    ((order ⟨(s,.inl g),⟨v,.inl false⟩⟩ z).val)
    ((bitsAt ⟨(s,.inl g),⟨v,.inl false⟩⟩).tag z)
    (Z.bank_role_cases key m p hp fit ⟨(s,.inl g),⟨v,.inl false⟩⟩ z)

theorem good_root_row (s : Bool) (g : (R).Good) (v : Fin (2^Z.n))
    (z : (bitsAt ⟨(s,.inl g),⟨v,.inl false⟩⟩).Node) :
    let slot:=(order ⟨(s,.inl g),⟨v,.inl false⟩⟩ z).val
    ∃r : Fin (Z.circuit s g).layers,slot/m=r.val ∧
      role ((bitsAt ⟨(s,.inl g),⟨v,.inl false⟩⟩).tag z)=rotorNumber ((Z.circuit s g).rotation r) v := by
  have project {layers : ℕ} (rotation : Fin layers → Equiv.Perm (Fin (2^Z.n)))
      (slot : ℕ) (tag : CanonicalTag (2^Z.n))
      (found : ∃ r : Fin layers, ∃ j : Fin m,
        slot = m*r.val+j.val ∧ tag = .inl (rotation r,v)) :
      ∃ r : Fin layers, slot/m = r.val ∧ role (n := Z.n) tag = rotorNumber (n := Z.n) (rotation r) v := by
    obtain ⟨r,j,number,hTag⟩ := found
    refine ⟨r,?_,congrArg (role (n := Z.n)) hTag⟩
    rw [number, Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  exact project (layers := (Z.circuit s g).layers) (Z.circuit s g).rotation
    ((order ⟨(s,.inl g),⟨v,.inl false⟩⟩ z).val)
    ((bitsAt ⟨(s,.inl g),⟨v,.inl false⟩⟩).tag z)
    (Z.good_root_role key m p hp fit s g v z)

theorem good_end_empty (s : Bool) (g : (R).Good) (v : Fin (2^Z.n)) :
    IsEmpty ((bitsAt ⟨(s,.inl g),⟨v,.inl true⟩⟩).Node):=
  ⟨fun z=>Z.bank_role_cases key m p hp fit ⟨(s,.inl g),⟨v,.inl true⟩⟩ z⟩

theorem good_tap_role (s : Bool) (g : (R).Good) (v : Fin (2^Z.n)) (leg)
    (z : (bitsAt ⟨(s,.inl g),⟨v,.inr leg⟩⟩).Node) :
    let arity:=((program ⟨(s,.inl g),⟨v,.inr leg⟩⟩).op z).arity
    (role ((bitsAt ⟨(s,.inl g),⟨v,.inr leg⟩⟩).tag z)=if arity=2 then 5 else 3) ∧ (arity=1 ∨ arity=2):=
  Z.bank_role_cases key m p hp fit ⟨(s,.inl g),⟨v,.inr leg⟩⟩ z

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
