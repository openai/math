import OAI.Hierarchy.DescentResetLaneIssue
import OAI.Hierarchy.DescentResetLocalRoster
import OAI.Hierarchy.DescentPrivateLocalRoster
import OAI.Hierarchy.DescentIssuedRotorRoles

namespace OAI
/-! # A good rotor's argument cable in the receiver's bounded private candidate directory -/
namespace Hierarchy.DescentRotorOperandTicket
open DescentResetLocalRoster DescentResetHostSize DescentResetCableSlots DescentResetLaneIssue
open DescentLaneGates DescentBatchedRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open DescentRotor DescentRouterSlots Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2000000


/-- One numeric slot in the private sector of the receiver's resident table.
    Neither the previous vertex ID nor the public coarse group is present. -/
def candidate {n h : ℕ} (G : Graph n h) (Ht r Y : ℕ) (side : Bool) (root : Code r)
    (e : (DescentCommonPalette.rotor G).Edge) :=
  localPrivateId r Y (max (Fintype.card (DescentCommonPalette.rotor G).Edge) (2^(Ht+1)))
    (side,.inl root,DescentResetCableSlots.rotor Ht G e)

def lookup {n h : ℕ} {Q : Type} (G : Graph n h) (Ht r Y : ℕ) (side : Bool) (root : Code r) :
    (DescentCommonPalette.rotor G).Edge⊕Q→Option ℕ
  | .inl e=>some (candidate G Ht r Y side root e).val
  | .inr _=>none

theorem bounded {n h : ℕ} (G : Graph n h) (Ht r Y : ℕ) (side : Bool) (root : Code r)
    (e : (DescentCommonPalette.rotor G).Edge) :
    (candidate G Ht r Y side root e).val<2*(rootSlots r Y*
      max (Fintype.card (DescentCommonPalette.rotor G).Edge) (2^(Ht+1))) :=
  (candidate G Ht r Y side root e).isLt

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => m*p
local notation "src" => fun e : Item contact owner s w => first (root contact input site owner s w align e)
local notation "dst" => fun e : Item contact owner s w => last (link contact owner s w e)
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers C₀ b u
local notation "A" => DescentGoodRouter.device D u contact input site owner align s w G first last P
local notation "sz" => tapBits D u G P
local notation "prg" => program D m p hp contact input site owner align s w G first last P key
local notation "tapAt" => tapLane D m p hp contact input site owner align s w G first last P
local notation "RT" => rootLane D m p hp contact input site owner align s w G first last P
variable (Ht layers Y : ℕ) (rootCode : Code layers)
local notation "idAt" => candidate G Ht layers Y s rootCode
local notation "bareEdge" => (DescentCommonPalette.rotorEdgeEquiv G D P.layers C₀ b (m*p)).symm
local notation "readAt" => fun a => lookup G Ht layers Y s rootCode (Sum.map (bareEdge) id a)

omit [Fintype R] in
theorem root_operand (v : Fin (2^n)) (rr : Fin P.layers) (batch : Fin m) (t : RowBit G.arcs C₀ b v) :
    let l:=((prg ⟨v,.inl false⟩).op (rr,batch)).arg (rowSerial G.arcs C₀ b v t)
    readAt (Sum.map Subtype.val Subtype.val l.port)=some (idAt (.inr ⟨v,0⟩)).val := by
  have wire:=congrArg Prod.fst (root_fields D m p hp contact input site owner align s w G first last P key v rr batch t)
  exact congrArg (readAt) wire

omit [Fintype R] in
theorem tap_operand (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) (t : SpineRow (r:=P.layers) (m:=m) (sz v)) (j : Fin 2) :
    let l:=((prg ⟨v,.inr i⟩).op (.inl t)).arg j
    readAt (Sum.map Subtype.val Subtype.val l.port)=
      some (idAt (bareEdge (.inr ⟨v,if j=0 then i.castSucc else i.succ⟩))).val := by
  rw [tap_spine_operand]
  have wire:=congrArg Prod.fst (tap_fields D m p hp contact input site owner align s w G first last P v i (decide (j=0)) t)
  refine (congrArg (readAt) wire).trans ?_
  fin_cases j <;> rfl

private theorem first_wire {Q : Type} {width : Q→ℕ} {p Y : ℕ} (l : Lane p width) (which : LaneSource p width)
    (j : Fin ((equalOp (Y:=Y) (.wire l) which).arity)) (atZero : j.val=0) :
    (equalOp (Y:=Y) (.wire l) which).arg j=l := by
  cases which with
  | fixed z=>rfl
  | wire t=>
    change Fin 2 at j
    exact ite_eq_left (Fin.ext atZero)

omit [Fintype R] in
/-- On the selector tap operand zero always reads the preceding path cable. -/
theorem select_back (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) (t : Block P.layers m (sz v i))
    (j : Fin (((prg ⟨v,.inr i⟩).op (.inr t)).arity)) (atZero : j.val=0) :
    let l:=((prg ⟨v,.inr i⟩).op (.inr t)).arg j
    readAt (Sum.map Subtype.val Subtype.val l.port)=some (idAt (bareEdge (.inr ⟨v,i.castSucc⟩))).val := by
  let back:=tapAt v i true ⟨i,t⟩
  let other:=tapLegLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp v i t.1 t.2.1 t.2.2
  have same : ((prg ⟨v,.inr i⟩).op (.inr t)).arg j=back:=first_wire (Y:=2^n) back other j atZero
  have wire:=congrArg Prod.fst (tap_fields D m p hp contact input site owner align s w G first last P v i true ⟨i,t⟩)
  refine (congrArg (fun l=> (readAt) (Sum.map Subtype.val Subtype.val l.port)) same).trans ?_
  exact congrArg (readAt) wire

omit [Fintype R] in
/-- Either direction of a supply leg has the same local private cable number.
    The coordinate and its stride are issued by private_supply_fields. -/
theorem supply_operand (e : (H).Edge) (dir : Bool) (rr : Fin P.layers) (k : Fin m) (j : Fin (C₀*b)) :
    let l:=legLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp (.inr (e,dir)) rr k j
    (match l with | .fixed _=>none | .wire l'=>readAt (Sum.map Subtype.val Subtype.val l'.port))=
       some (idAt (.inl e)).val := by
  dsimp only
  have reading:=private_supply_fields D m p hp contact input site owner align s w G first last P key e dir rr k j
  cases atLane : legLane D u contact input site owner align s w G first last P key
      (m:=m) (p:=p) rfl hp (.inr (e,dir)) rr k j with
  | fixed z =>
    rw [atLane] at reading
    contradiction
  | wire v =>
    rw [atLane] at reading
    have port:=congrArg Prod.fst (Option.some.inj reading)
    exact congrArg (readAt) port

private theorem right_wire {Q : Type} {width : Q→ℕ} {p Y : ℕ} (left : Lane p width) (other : LaneSource p width)
    (j : Fin ((equalOp (Y:=Y) (.wire left) other).arity)) (later : j.val≠0) :
    other=.wire ((equalOp (Y:=Y) (.wire left) other).arg j) := by
  cases other with
  | fixed z=>have room:=j.isLt;change j.val<1 at room;omega
  | wire t=>
    change Fin 2 at j
    change LaneSource.wire t = LaneSource.wire (if j=0 then left else t)
    rw [ite_eq_right (fun eqn=>later (congrArg Fin.val eqn))]

omit [Fintype R] in
/-- Nonzero argument ordinal proves there really is a second wire, even though vacant focus
    positions have only one argument and print no pointer of their own. -/
theorem select_focus (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) (t : Block P.layers m (sz v i))
    (j : Fin (((prg ⟨v,.inr i⟩).op (.inr t)).arity)) (later : j.val≠0) :
    tapLegLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp v i t.1 t.2.1 t.2.2=
      .wire (((prg ⟨v,.inr i⟩).op (.inr t)).arg j) :=
  right_wire (Y:=2^n) (tapAt v i true ⟨i,t⟩) _ j later

def idRead (q : (A).Site) (l : LaneSource p (boundaryWidth A q)) : Option ℕ :=
  match l with
  | .fixed _=>none
  | .wire t=> readAt (Sum.map Subtype.val Subtype.val t.port)

omit [Fintype R] in
private theorem shift_id {q q' : (A).Site} (eqn : q=q') (l : LaneSource p (boundaryWidth A q)) :
    idRead D m p contact input site owner align s w G first last P Ht layers Y rootCode q' (eqn ▸ l)=
    idRead D m p contact input site owner align s w G first last P Ht layers Y rootCode q l := by
  cases eqn;rfl

omit [Fintype R] in
theorem selected_supply (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) (t : Block P.layers m (sz v i))
    (j : Fin (((prg ⟨v,.inr i⟩).op (.inr t)).arity)) (later : j.val≠0) (e : (H).Edge) (dir : Bool)
    (socket : name H v i=.inr (e,dir)) :
    let l:=((prg ⟨v,.inr i⟩).op (.inr t)).arg j
    readAt (Sum.map Subtype.val Subtype.val l.port)=some (idAt (.inl e)).val := by
  let fetch:=legLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp
  let proj:=idRead D m p contact input site owner align s w G first last P Ht layers Y rootCode
  have raw (leg : Leg H) (same : leg=.inr (e,dir)) (bit : Fin (legBits D u G P leg)) :
      proj _ (fetch leg t.1 t.2.1 bit)=some (idAt (.inl e)).val := by
    subst leg
    have known:=supply_operand D m p hp contact input site owner align s w G first last P key Ht layers Y rootCode e dir t.1 t.2.1 bit
    dsimp only [proj,fetch,idRead]
    dsimp only at known
    cases atLane : legLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp (.inr (e,dir)) t.1 t.2.1 bit <;> rw [atLane] at known <;> exact known
  have focus:=select_focus D m p hp contact input site owner align s w G first last P key v i t j later
  change proj _ (.wire (((prg ⟨v,.inr i⟩).op (.inr t)).arg j))=_
  refine (congrArg (proj _) focus.symm).trans ?_
  unfold tapLegLane
  exact (shift_id D m p contact input site owner align s w G first last P Ht layers Y rootCode _ _).trans
    (raw (name H v i) socket t.2.2)


end
end Hierarchy.DescentRotorOperandTicket

end OAI
