import OAI.Hierarchy.DescentOperandRoleNumbers
import OAI.Hierarchy.DescentOperandRouteView
import OAI.Hierarchy.DescentOperandArmInverse
import OAI.Hierarchy.DescentPhysicalSiteVolume

namespace OAI
/-! # Native selectors for old and newly installed scalar operand rows -/

namespace Hierarchy.DescentOperandPhysicalInput
open Computability.BorderVNP.Crossing DescentKernelHistory DescentSixParty GadgetNetwork DescentHistoryOrder
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentOrdinaryDestRAM DescentOperandRouteRAM
open scoped Fin.CommRing Classical
noncomputable section

variable {F P I : Type} [Field F] [Fintype I] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F) (pick : I × Fin 2 ↪ W.graph.Edge)
variable (z : I→ℕ) (profiles : I→Profile G.C)
local notation "N" => W.graph
local notation "sw" => branchWidth G z profiles
local notation "M" => physical N pick sw
variable (edge : W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))

/-- The inverse table redirects only selected destination operands. -/
def destName (W : MarkedWorld F d P bits) (pick : I × Fin 2 ↪ W.graph.Edge)
    (edge : W.graph.Edge ≃ Fin (Fintype.card W.graph.Edge)) (pair : I ≃ Fin (Fintype.card I)) (e : W.graph.Edge) : ℕ :=
  match selected W.graph pick e with
  | none=>(edge e).val
  | some (i,t)=>Fintype.card W.graph.Edge+10*(pair i).val+t.val

def carriedName (W : MarkedWorld F d P bits) (pick : I × Fin 2 ↪ W.graph.Edge)
    (edge : W.graph.Edge ≃ Fin (Fintype.card W.graph.Edge)) (pair : I ≃ Fin (Fintype.card I)) (node : W.graph.Site) (e : W.graph.Edge) : ℕ :=
  if W.graph.src e=node then (edge e).val else destName W pick edge pair e

open private Hierarchy.DescentKernelHistory.oldTarget from OAI.Hierarchy.DescentGadgetHistory in
theorem carried_public (u : (N).Site) (e : Incident N u) (t : Fin ((N).width e.val)) :
    let bit:=carriedBit G W.toWorld pick z profiles u ⟨.inl e,t⟩
    (match bit.1 with
     | .inl cable=>some (MarkedWorld.edgeNumber W edge pair cable.val)
     | .inr _=>none)=some (carriedName W pick edge pair u e.val) ∧ bit.2.val=t.val := by
  let number : Boundary (M) (.inl u) → Option ℕ
    | .inl cable => some (MarkedWorld.edgeNumber W edge pair cable.val)
    | .inr _ => none
  constructor
  · change number (oldBoundary N pick sw u (.inl e))=some (carriedName W pick edge pair u e.val)
    by_cases source : (N).src e.val=u
    · rw [carriedName,ite_eq_left source]
      have routed : oldBoundary N pick sw u (.inl e)=
          .inl ⟨.inl e.val,Or.inl (congrArg Sum.inl source)⟩ := dite_eq_left source
      exact congrArg number routed
    · rw [carriedName,ite_eq_right source]
      let dst := e.property.resolve_left source
      let name : Option (I × Fin 2) → ℕ
        | none => (edge e.val).val
        | some (i,k) => Fintype.card W.graph.Edge+10*(pair i).val+k.val
      have read (o : Option (I × Fin 2)) (found : selected N pick e.val=o) :
          number (Hierarchy.DescentKernelHistory.oldTarget N pick sw u e.val dst o found)=some (name o) := by
        cases o with
        | none => rfl
        | some ij => rcases ij with ⟨i,k⟩; rfl
      have routed : oldBoundary N pick sw u (.inl e)=
          Hierarchy.DescentKernelHistory.oldTarget N pick sw u e.val dst (selected N pick e.val) rfl := dite_eq_right source
      exact (congrArg number routed).trans (read _ rfl)
  · rfl

def pickedOrd (W : MarkedWorld F d P bits) (pick : I × Fin 2 ↪ W.graph.Edge)
    (edge : W.graph.Edge ≃ Fin (Fintype.card W.graph.Edge)) (pair : I ≃ Fin (Fintype.card I)) : Fin (Fintype.card I) × Fin 2 ↪ Fin (Fintype.card W.graph.Edge) :=
  ⟨fun a=>edge (pick (pair.symm a.1,a.2)),by
    rintro ⟨i,t⟩ ⟨j,s⟩ h
    have eqn:=pick.injective (edge.injective h)
    have left:=pair.symm.injective (congrArg Prod.fst eqn)
    have right:=congrArg Prod.snd eqn
    exact Prod.ext left right⟩

omit [_root_.Field F] in
theorem inverse_read (L : DescentOperandArmInverse.Layout) {w : ℕ}
    (fits : DescentOperandArmInverse.Fits L w (Fintype.card W.graph.Edge) (Fintype.card I))
    (m : Memory w) (e : (N).Edge) :
    DescentOperandArmInverse.output L (pickedOrd W pick edge pair) m (L.dest+(edge e).val)=
      (destName W pick edge pair e:Computability.VPVNP.BurstRAM.Word w) := by
  cases sel : selected N pick e with
  | none=>
    simp only [destName,sel]
    apply DescentOperandArmInverse.untouched _ _ fits
    intro i t ordered
    have h : e=pick (pair.symm i,t) := edge.injective ordered
    rw [h,selected_pick] at sel
    contradiction
  | some x=>
    obtain ⟨i,t⟩:=x
    have eqn:=selected_spec N pick sel
    have ordinal : pickedOrd W pick edge pair (pair i,t) = edge e := by
      change edge (pick ((pair.symm (pair i)),t)) = edge e
      rw [pair.symm_apply_apply,eqn]
    simpa only [destName,sel, DescentOperandArmInverse.addr,DescentOperandArmInverse.arm,
      ordinal] using DescentOperandArmInverse.selected L (pickedOrd W pick edge pair) fits m (pair i) t

def bornName (W : MarkedWorld F d P bits) (pick : I × Fin 2 ↪ W.graph.Edge)
    (edge : W.graph.Edge ≃ Fin (Fintype.card W.graph.Edge)) (pair : I ≃ Fin (Fintype.card I)) (i : I) : Role→ℕ
  | .original t=>(edge (pick (i,t))).val
  | .arm t=>Fintype.card W.graph.Edge+10*(pair i).val+t.val
  | .supply t=>Fintype.card W.graph.Edge+10*(pair i).val+2+t.val

theorem born_public (i : I) (j : Fin 6) (a : Fin (Fintype.card (RolePort j))) :
    (match nativeRole N pick sw i j ((roleIndex j).symm a) with
      | .inl cable=>some (MarkedWorld.edgeNumber W edge pair cable.val)
      | .inr _=>none)=some (bornName W pick edge pair i (role ((roleIndex j).symm a))) := by
  generalize (roleIndex j).symm a=slot
  rcases slot with (h|h)|(h|h) <;> rfl

def roleAddress (j : Fin 6) (a : Fin (Fintype.card (RolePort j))) := 8*j.val+a.val
theorem roleAddress_lt (j : Fin 6) (a : Fin (Fintype.card (RolePort j))) :
    roleAddress j a < 48 := by have:=physical_role_arity j;have:=j.isLt;have:=a.isLt;unfold roleAddress;omega

/-- The fixed forty-eight-address catalogue is shared by all used pairs and all profiles. -/
def catalogue (i : ℕ) : Role :=
  if j : i/8<6 then
    let party : Fin 6:=⟨i/8,j⟩
    if a : i%8<Fintype.card (RolePort party) then roleAt party ⟨i%8,a⟩ else .arm 0
  else .arm 0

theorem catalogue_at (j : Fin 6) (a : Fin (Fintype.card (RolePort j))) :
    catalogue (roleAddress j a)=roleAt j a := by
  have small : a.val<8 := a.isLt.trans_le (physical_role_arity j)
  have div : roleAddress j a/8=j.val := by unfold roleAddress;omega
  have mod : roleAddress j a%8=a.val := by unfold roleAddress;omega
  have hi := div.trans_lt j.isLt
  let party : Fin 6 := ⟨roleAddress j a/8,hi⟩
  have equal : party=j := Fin.ext div
  have slotBound : roleAddress j a%8<Fintype.card (RolePort party) := by
    rw [equal,mod]
    exact a.isLt
  have sameRole (u : Fin 6) (b : Fin (Fintype.card (RolePort u)))
      (hu : u=j) (hb : b.val=a.val) : roleAt u b=roleAt j a := by
    subst u
    exact congrArg (roleAt j) (Fin.ext hb)
  unfold catalogue
  rw [dite_eq_left hi]
  change (if h : roleAddress j a%8<Fintype.card (RolePort party) then
    roleAt party ⟨roleAddress j a%8,h⟩ else .arm 0)=roleAt j a
  rw [dite_eq_left slotBound]
  exact sameRole party _ equal mod

private def add (a b : Expr) := Expr.op .add a b
def carried (oldEdge oldNode : Expr) (sources inverse : Bank) : Expr :=
  .branch .eq (.lookup sources oldEdge) oldNode oldEdge (.lookup inverse oldEdge)

structure BornBanks where
  pairs : Bank
  roleKinds : Bank
  roleSlots : Bank

def born (s : BornBanks) (ne : ℕ) (pairAddress party operand : Expr) : Expr :=
  let select:=add (times 8 party) operand
  let k:=Expr.lookup s.roleKinds select
  let t:=Expr.lookup s.roleSlots select
  let old:=Expr.lookup s.pairs (add (times 9 pairAddress) (add (.lit 1) t))
  let start:=add (.lit ne) (times 10 pairAddress)
  .branch .eq k (.lit 0) old (.branch .eq k (.lit 1) (add start t) (add (add start (.lit 2)) t))

omit [_root_.Field F] in
theorem carried_read {w : ℕ} (m : Memory w) (row : Computability.VPVNP.BurstRAM.Word w) (sources inverse : Bank)
    (oldEdge oldNode : Expr) (id : (N).Site↪ℕ) (e : (N).Edge) (u : (N).Site)
    (es : oldEdge.eval m row=(edge e).val) (us : oldNode.eval m row=id u)
    (src : sources.read m (edge e).val=id ((N).src e))
    (table : inverse.read m (edge e).val=destName W pick edge pair e)
    (range : ∀v,id v<2^w) :
    (carried oldEdge oldNode sources inverse).eval m row=(carriedName W pick edge pair u e:Computability.VPVNP.BurstRAM.Word w) := by
  have eqn : (id ((N).src e):Computability.VPVNP.BurstRAM.Word w)=(id u:Computability.VPVNP.BurstRAM.Word w) ↔ (N).src e=u := by
    constructor
    · intro h;apply id.injective
      simpa only [Fin.val_cast_of_lt (range _)] using congrArg Fin.val h
    · rintro rfl;rfl
  by_cases oldSource : W.graph.src e=u
  · simp [carried,Expr.eval,DescriptorExpr.Comparison.test,es,us,src,carriedName,oldSource]
  · have distinct := mt eqn.mp oldSource
    simp [carried,Expr.eval,DescriptorExpr.Comparison.test,es,us,src,table,carriedName,oldSource,distinct]

omit [_root_.Field F] in
theorem born_read {w : ℕ} (s : BornBanks) (m : Memory w) (atRow : Computability.VPVNP.BurstRAM.Word w)
    (pairAddress party operand : Expr) (i : I) (j : Fin 6) (a : Fin (Fintype.card (RolePort j)))
    (pidx : pairAddress.eval m atRow=(pair i).val) (jdx : party.eval m atRow=j.val)
    (adx : operand.eval m atRow=a.val)
    (ks : ∀k : ℕ,k<48→s.roleKinds.read m (k:Computability.VPVNP.BurstRAM.Word w)=(catalogue k).kind)
    (ts : ∀k : ℕ,k<48→s.roleSlots.read m (k:Computability.VPVNP.BurstRAM.Word w)=(catalogue k).slot)
    (pairs : ∀t : Fin 2,s.pairs.read m ((9*(pair i).val+(1+t.val):ℕ):Computability.VPVNP.BurstRAM.Word w)=(edge (pick (i,t))).val)
    (wide : 2<2^w) :
    (born s (Fintype.card W.graph.Edge) pairAddress party operand).eval m atRow=
      (bornName W pick edge pair i (roleAt j a):Computability.VPVNP.BurstRAM.Word w) := by
  let address:=add (times 8 party) operand
  have addressRead : address.eval m atRow=((roleAddress j a:ℕ):Computability.VPVNP.BurstRAM.Word w) := by
    change (times 8 party).eval m atRow+operand.eval m atRow=_
    rw [times_eval,jdx,adx];simp [roleAddress]
  have kinds : (Expr.lookup s.roleKinds address).eval m atRow=((roleAt j a).kind:Computability.VPVNP.BurstRAM.Word w) := by
    change s.roleKinds.read m (address.eval m atRow)=_
    rw [addressRead,ks _ (roleAddress_lt j a),catalogue_at]
  have slots : (Expr.lookup s.roleSlots address).eval m atRow=((roleAt j a).slot:Computability.VPVNP.BurstRAM.Word w) := by
    change s.roleSlots.read m (address.eval m atRow)=_
    rw [addressRead,ts _ (roleAddress_lt j a),catalogue_at]
  have neq (x y : ℕ) (hx : x<2^w) (hy : y<2^w) (h : x≠y) : (x:Computability.VPVNP.BurstRAM.Word w)≠(y:Computability.VPVNP.BurstRAM.Word w) := by
    intro heq;apply h
    simpa only [Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy] using congrArg Fin.val heq
  have d10 : (1:Computability.VPVNP.BurstRAM.Word w)≠0 := neq 1 0 (by omega) (by omega) (by decide)
  have d20 : (2:Computability.VPVNP.BurstRAM.Word w)≠0 := neq 2 0 (by omega) (by omega) (by decide)
  have d21 : (2:Computability.VPVNP.BurstRAM.Word w)≠1 := neq 2 1 (by omega) (by omega) (by decide)
  let kindWord := (Expr.lookup s.roleKinds address).eval m atRow
  let slotWord := (Expr.lookup s.roleSlots address).eval m atRow
  let start : Computability.VPVNP.BurstRAM.Word w :=
    (Fintype.card W.graph.Edge : Computability.VPVNP.BurstRAM.Word w)+(times 10 pairAddress).eval m atRow
  change (if kindWord == 0 then
    s.pairs.read m ((times 9 pairAddress).eval m atRow+(1+slotWord))
    else if kindWord == 1 then start+slotWord else (start+2)+slotWord)=_
  change kindWord=_ at kinds
  change slotWord=_ at slots
  rw [kinds,slots]
  simp only [start,times_eval,pidx]
  cases rk : roleAt j a with
  | original t=>
    have read:=pairs t
    push_cast at read
    simpa [Role.kind,Role.slot,bornName] using read
  | arm t | supply t=>
    simp [Role.kind,Role.slot,bornName,d10,d20,d21]
end
end Hierarchy.DescentOperandPhysicalInput

end OAI
