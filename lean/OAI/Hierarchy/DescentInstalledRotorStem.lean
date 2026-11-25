import OAI.Hierarchy.DescentClosedProgramArgument
import OAI.Hierarchy.DescentInstalledPortKeys
import OAI.Hierarchy.DescentCalendarPublicSocketField
import OAI.Hierarchy.DescentRotorApertureLane
import OAI.Hierarchy.DescentRotorActualAperture

namespace OAI
/-! The public source leg of an occupied good rotor tap has the original
attached bank port. Its physical block keeps the same ordinal under installation. -/
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
local notation "src" => (fun x : Item contact owner s w => first (root contact input site owner s w align x))
local notation "dst" => (fun x : Item contact owner s w => last (link contact owner s w x))
local notation "E" => Item contact owner s w
local notation "A" => DescentGoodRouter.device D (m*p) contact input site owner align s w G first last P
local notation "H" => Physical.host G.arcs D P.layers C₀ b (m*p)
local notation "old" => DescentOrderedReset.itemKey key contact owner s w

open DescentOrderedReset
open DescentRotorOperandQueryROM.Shape
local notation "ord" => Ordered.orderedAddress old src dst hw
local notation "selected" => fun (side : Bool) (v : Fin (2^n)) (r : Fin P.layers) (j : Fin b) (e : E) => ((if side then dst e else src e)=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j)
local notation "get" => publicTapLane D (m*p) contact input site owner align s w G first last P key
  (m:=m) (p:=p) rfl hp

open DescentNamedContact DescentPublicOperandPhysicalPorts DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
local notation "u" => m*p
local notation "request" side:arg v:arg r:arg k:arg j:arg a:arg => (⟨side,v,(r).val,(k).val,(j).val,a⟩ : Mouth n)
local notation "prior" side:arg v:arg r:arg k:arg j:arg a:arg e:arg => Config.earlierCount src dst old (request side v r k j a) e
local notation "atSide" side:arg v:arg => DescentRotorOperandRanks.At src dst (fun z=>(if side then z.2 else z.1)=v)
private abbrev stemSourceWidth {Port : Type} {packet : ℕ} {width : Port → ℕ} (_ : LaneSource packet width) := width

omit [Fintype R] in
theorem public_stem_lane (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m)
    (j : Fin b) (e : E) (arrived : selected false v r j e) :
    ∃ (l : Lane p (stemSourceWidth (get false v r k j)))
      (atSite : (A).attach (rootSlot D contact input site owner (fun _ : I=>(m*p)) s w (root contact input site owner s w align e))=
        tap H (.inl (v,false))),
      get false v r k j=.wire l ∧ l.port=.inr ⟨rootSlot D contact input site owner (fun _ : I=>(m*p)) s w
        (root contact input site owner s w align e),atSite⟩ :=by
  change src e=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j at arrived
  obtain ⟨rfl,rfl,rfl⟩:=arrived
  let item : {i : E // src i=src e}:=⟨e,rfl⟩
  let l:=falseLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl _ k item hp
  have issued : get false (src e) (P.choose (ord e).1) k (ord e).2=.wire l :=by
    have focusEq : Ordered.focus ord (fun z=>(P.choose z,z.1)) src (fun _=>rfl)
        (P.choose (ord e).1) (src e) (ord e).2=.inr item :=
      realized_focus G P old false e
    exact congrArg (focusLane (fun t => falseLane D (m*p) contact input site owner align s w G first last P key
      (m:=m) (p:=p) rfl (src e) k t hp)) focusEq
  have siteAt : (A).attach (rootSlot D contact input site owner (fun _ : I=>(m*p)) s w (root contact input site owner s w align e))=
      tap H (.inl (src e,false)) :=by
    change tap H (.inl (DescentGoodRouter.position D (m*p) contact input site owner s w first last _))=_
    apply congrArg (fun q=>tap H (.inl q))
    simp [DescentGoodRouter.position]
  exact ⟨l,siteAt,issued,rfl⟩


omit [Fintype C] [Fintype R] [Fintype W] in
/-- Every donor selected after advancing inside the same tap lies at
its native chronological rank in the original attached input port. -/
theorem source_fibre_rank (req : Mouth n) (leg : req.pin=false) (firstItem donor : E)
    (begins : src firstItem=req.vertex) (endsAt : src donor=req.vertex) :
    ∃item : DescentNamedContact.Fibre (input s) (input s firstItem.val),
      item.val=donor.val ∧
      (DescentOrderedWords.before (fibreKey key (input s) (input s firstItem.val)) item).card=
        Config.earlierCount src dst old req donor :=by
  have meet : src donor=src firstItem:=endsAt.trans begins.symm
  have same : input s donor.val=input s firstItem.val:=congrArg Subtype.val (first.injective meet)
  have native:=root_prefix contact input site owner align s w first key donor
  have atDonor : Config.earlierCount src dst old req donor=
      (DescentOrderedWords.before (fibreKey key (input s) (input s donor.val)) ⟨donor.val,rfl⟩).card :=by
    rcases req with ⟨pin,vertex,layer,batch,digit,within⟩
    change pin=false at leg
    change src donor=vertex at endsAt
    subst pin
    cases endsAt
    exact native
  have rankAt (addr : R) (haddr : input s donor.val=addr) :
      (DescentOrderedWords.before (fibreKey key (input s) addr) ⟨donor.val,haddr⟩).card=
        Config.earlierCount src dst old req donor :=by
    cases haddr
    exact atDonor.symm
  exact ⟨⟨donor.val,same⟩,rfl,rankAt _ same⟩

omit [Fintype R] in
/-- A covered source request carries the original input pin and the
complete physical p-word ordinal, including the offset inside the instruction. -/
theorem public_stem_block (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m)
    (j : Fin b) (digit : ℕ) (e : E) (arrived : selected false v r j e)
    (size : ∀a,boundaryWidth A (tap H (.inl (v,false))) a=
      (boundaryWidth A (tap H (.inl (v,false))) a/p)*p)
    (covered : digit< min 2 (Fintype.card (atSide false v)*m-(prior false v r k j digit e*m+k.val))) :
    ∃(l : Lane p (boundaryWidth A (tap H (.inl (v,false)))))
      (atSite : (A).attach (rootSlot D contact input site owner (fun _ : I=>u) s w (root contact input site owner s w align e))=
        tap H (.inl (v,false)))
      (offset : Fin (l.count (fun a=>boundaryWidth A (tap H (.inl (v,false))) a/p))),
      get false v r k j=.wire l ∧
      (laneBlock _ size hp l offset).port=.inr ⟨_,atSite⟩ ∧
      offset.val=digit ∧
      (laneBlock _ size hp l offset).block=prior false v r k j digit e*m+k.val+digit :=by
  obtain ⟨l,atSite,live,pin⟩:=public_stem_lane D m p hp contact input site owner align s w G first last P key v r k j e arrived
  obtain ⟨other,otherAt,beg,stride,extent⟩:=public_lane_at D m p hp contact input site owner align s w G first last P key
    false v r k j digit e arrived
  have eqLane : l=other:=LaneSource.wire.inj (live.symm.trans otherAt)
  subst other
  have start : l.bundleStart=prior false v r k j digit e*m+k.val:=by
    simp only [Lane.bundleStart,beg,Nat.mul_div_cancel _ hp]
  have inRange : digit<l.count (fun a=>boundaryWidth A (tap H (.inl (v,false))) a/p):=by
    have portWidth : boundaryWidth A (tap H (.inl (v,false))) l.port/p = Fintype.card (atSide false v)*m := extent
    simpa only [Lane.count,stride,portWidth,start] using covered
  refine ⟨l,atSite,⟨digit,inRange⟩,live,pin,rfl,?_⟩
  change l.bundleStart+digit=_
  rw [start]

end
end Hierarchy.DescentResetLaneIssue
namespace Hierarchy.DescentSixParty.ResetInput
open DescentBundleHistory DescentRetainedRangeDigits DescentBatchedBank
open Computability.BorderVNP.Crossing DescentRotor DescentChosenRouter DescentKernelHistory DescentResetGates
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "R" => Z.placement
local notation "chosen" => DescentChosenRouter.selected R Z.graph Z.positive Z.pay Z.circuit

local notation "rack" => DescentRouterBank.network d (R).contact (R).input (R).site (R).owner (fun _ : A.graph.Edge=>Z.unit)
local notation "devices" => fun u : (rack).Site=>DescentMixedRouter.device Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align (D:=d) (chosen u.1 u.2)
local notation "localProgram" => sizedLocal Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen
local notation "nodes" => sizedLocalNode Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen


theorem bank_word_stem (side : Bool) (root : (R).Good) (e : DescentChosenRouter.Cells R side root)
    (v : (devices (side,.inl root)).Site)
    (r : BlockRef p (boundaryWidth (devices (side,.inl root)) v))
    (atSite : (devices (side,.inl root)).attach (DescentRouterSlots.rootSlot d (R).contact (R).input (R).site (R).owner
      (fun _ : A.graph.Edge=>Z.unit) side (.inl root) (DescentRouterSlots.root (R).contact (R).input (R).site (R).owner
        side (.inl root) (R).align e))=v)
    (localPort : r.port=.inr ⟨_,atSite⟩) :
    ∃port,(Z.bankPorts ⟨(side,.inl root),v⟩).slot r.port=Sum.inr port ∧
      port.val=(side,(R).input side e.val) ∧
      ((Z.bankPorts ⟨(side,.inl root),v⟩).wordBlock r).block=r.block :=by
  rw [localPort]
  exact ⟨_,rfl,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
