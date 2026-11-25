import OAI.Hierarchy.DescentPublicOperandPhysicalPorts
import OAI.Hierarchy.DescentResetLaneIssue
import OAI.Hierarchy.DescentEqualityRangeDigits

namespace OAI
/-! # Range digits at a real attached public rotor operand -/
namespace Hierarchy.DescentResetLaneIssue
open DescentLaneGates DescentBatchedRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open DescentRotor DescentRouterSlots Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun x : Item contact owner s w => first (root contact input site owner s w align x))
    (fun x : Item contact owner s w => last (link contact owner s w x)) pay) (key : I↪Fin num)
local notation "sourceSite" => (fun x : Item contact owner s w => first (root contact input site owner s w align x))
local notation "targetSite" => (fun x : Item contact owner s w => last (link contact owner s w x))
local notation "Index" => Item contact owner s w
local notation "socketKey" => DescentOrderedReset.itemKey key contact owner s w


open DescentPublicOperandPhysicalPorts DescentOrderedReset DescentRetainedRangeDigits DescentBundleHistory

private abbrev portUnits {Port : Type} {width : Port → ℕ} {packet : ℕ}
    (_ : Lane packet width) (port : Port) := width port / packet

omit [Fintype R] in
/-- The consecutive words recorded for the public source come from the original
ordered socket, with the last item truncated at its actual width. -/
theorem source_range (v : Fin (2^n)) (k : Fin m) (e : {j : Index // sourceSite j=v}) :
    let lane:=falseLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl v k e hp
    let earlier : ℕ := (Finset.univ.filter (fun z : {j : Index // sourceSite j=v}=>key z.val.val<key e.val.val)).card
    let amount:=Fintype.card {j : Index // sourceSite j=v}*m
    lane.start=(earlier*m+k.val)*p ∧ lane.stride=1 ∧ portUnits lane lane.port=amount ∧
      lane.count (portUnits lane)=min 2 (amount-(earlier*m+k.val)) :=by
  rcases e with ⟨e,h₁⟩
  subst v
  let item : {j : Index // sourceSite j=sourceSite e}:=⟨e,rfl⟩
  let lane:=falseLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl (sourceSite e) k item hp
  let units := portUnits lane
  have rootFields:=public_source_fields D m p hp contact input site owner align s w G first last P key (sourceSite e) k item
  have begins:=congrArg (fun a : _×ℕ×ℕ=>a.2.1) rootFields
  have step:=congrArg (fun a : _×ℕ×ℕ=>a.2.2) rootFields
  have starts : lane.start=((Finset.univ.filter (fun z : {j : Index // sourceSite j=sourceSite e}=>key z.val.val<key e.val)).card*m+k.val)*p :=by
    rw [root_prefix contact input site owner align s w first key e]
    exact begins
  have stride : lane.stride=1:=step
  have size : units lane.port=Fintype.card {j : Index // sourceSite j=sourceSite e}*m :=by
    exact root_units contact input site owner align s w first D m p hp e
  refine ⟨starts,stride,size,?_⟩
  change min (lane.stride+1) (units lane.port-lane.start/p)=_
  rw [starts,stride,size,Nat.mul_div_cancel _ hp]

omit [Fintype R] in
/-- The consecutive words recorded for the public target come from the original
ordered socket, with the last item truncated at its actual width. -/
theorem target_range (v : Fin (2^n)) (k : Fin m) (e : {j : Index // targetSite j=v}) :
    let lane:=trueLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl v k e hp
    let earlier : ℕ := (Finset.univ.filter (fun z : {j : Index // targetSite j=v}=>key z.val.val<key e.val.val)).card
    let amount:=Fintype.card {j : Index // targetSite j=v}*m
    lane.start=(earlier*m+k.val)*p ∧ lane.stride=1 ∧ portUnits lane lane.port=amount ∧
      lane.count (portUnits lane)=min 2 (amount-(earlier*m+k.val)) :=by
  rcases e with ⟨e,h₁⟩
  subst v
  let item : {j : Index // targetSite j=targetSite e}:=⟨e,rfl⟩
  let lane:=trueLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl (targetSite e) k item hp
  let units := portUnits lane
  have rootFields:=public_target_fields D m p hp contact input site owner align s w G first last P key (targetSite e) k item
  have begins:=congrArg (fun a : _×ℕ×ℕ=>a.2.1) rootFields
  have step:=congrArg (fun a : _×ℕ×ℕ=>a.2.2) rootFields
  have starts : lane.start=((Finset.univ.filter (fun z : {j : Index // targetSite j=targetSite e}=>key z.val.val<key e.val)).card*m+k.val)*p :=by
    rw [link_prefix contact owner s w last key e]
    exact begins
  have stride : lane.stride=1:=step
  have size : units lane.port=Fintype.card {j : Index // targetSite j=targetSite e}*m :=by
    exact link_units contact input site owner s w last D m p hp e
  refine ⟨starts,stride,size,?_⟩
  change min (lane.stride+1) (units lane.port-lane.start/p)=_
  rw [starts,stride,size,Nat.mul_div_cancel _ hp]


/-- On the genuine second (public) operand of a tap equality, only its
residue, stride and true cover are printed, once per covered word. -/
theorem second_range {B : Type} {width : B→ℕ} {p Y : ℕ} (positive : 0<p)
    (multiple : ∀j,width j=width j/p*p) (P : Program Y p width) (node : P.Node) (l r : Lane p width)
    (op : P.op node=equalOp (.wire l) (.wire r)) (phase : r.start%p=0) (stride : r.stride=1)
    (i : ℕ) (f : Fin 3) :
    atSlot (ofProgram (fun j=>width j/p) multiple positive P) node (l.count (fun j=>width j/p)+i) f=
      if i<r.count (fun j=>width j/p) then (if f.val=0 then 0 else if f.val=1 then 1 else r.count (fun j=>width j/p)) else 0 :=by
  rw [equality_slot _ multiple positive P node l r op]
  simp [laneCode,DescentRetainedRangeDigits.value,Lane.residue,phase,stride]

end
end Hierarchy.DescentResetLaneIssue

end OAI
