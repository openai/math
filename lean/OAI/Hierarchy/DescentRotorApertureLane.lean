import OAI.Hierarchy.DescentRotorPublicRanges
import OAI.Hierarchy.DescentRotorActualAperture

namespace OAI
/-! # An occupied rotor mouth reads the scheduled (DescentOrderedReset.itemKey key contact owner s w) wire and a vacant one reads its fixed bit -/
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

open DescentOrderedReset
open DescentRotorOperandQueryROM.Shape DescentResetPublicOperandBook
local notation "ord" => Ordered.orderedAddress socketKey sourceSite targetSite hw
local notation "selected" => fun (side : Bool) (v : Fin (2^n)) (r : Fin P.layers) (j : Fin b) (e : Index) => ((if side then targetSite e else sourceSite e)=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j)
local notation "get" => publicTapLane D (m*p) contact input site owner align s w G first last P key
  (m:=m) (p:=p) rfl hp

private abbrev sourceWidth {Port : Type} {packet : ℕ} {width : Port → ℕ} (_ : LaneSource packet width) := width

omit [Fintype R] in
/-- The physical control that built the selected tap and the reservation table
use the very same original rail. Its offset counts earlier rails in this port,
irrespective of the layer they use. -/
theorem public_lane_at (dir : Bool) (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m)
    (j : Fin b) (within : ℕ) (e : Index) (arrived : selected dir v r j e) :
    ∃ l : Lane p (sourceWidth (get dir v r k j)),get dir v r k j=.wire l ∧
      l.start=(Config.earlierCount sourceSite targetSite socketKey (⟨dir,v,r.val,k.val,j.val,within⟩ : Mouth n) e*m+k.val)*p ∧ l.stride=1 ∧
      sourceWidth (get dir v r k j) l.port/p=Fintype.card (DescentRotorOperandRanks.At sourceSite targetSite (fun z=>(if dir then z.2 else z.1)=v))*m:=by
  cases dir with
  | false =>
    change sourceSite e=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j at arrived
    obtain ⟨rfl,rfl,rfl⟩:=arrived
    let item : {i : Index // sourceSite i=sourceSite e}:=⟨e,rfl⟩
    refine ⟨falseLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl _ k item hp,?_,?_⟩
    · have focusEq : Ordered.focus ord (fun z=>(P.choose z,z.1)) sourceSite (fun _=>rfl)
          (P.choose (ord e).1) (sourceSite e) (ord e).2=.inr item :=
        realized_focus G P socketKey false e
      simp only [publicTapLane,focusEq,focusLane,Sum.elim_inr]
    · have info:=source_range D m p hp contact input site owner align s w G first last P key (sourceSite e) k item
      exact ⟨info.1,info.2.1,info.2.2.1⟩
  | true =>
    change targetSite e=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j at arrived
    obtain ⟨rfl,rfl,rfl⟩:=arrived
    let item : {i : Index // targetSite i=targetSite e}:=⟨e,rfl⟩
    refine ⟨trueLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl _ k item hp,?_,?_⟩
    · have focusEq : Ordered.focus ord (fun z=>(P.choose z,z.2.1)) targetSite (fun _=>rfl)
          (P.choose (ord e).1) (targetSite e) (ord e).2=.inr item :=
        realized_focus G P socketKey true e
      simp only [publicTapLane,focusEq,focusLane,Sum.elim_inr]
    · have info:=target_range D m p hp contact input site owner align s w G first last P key (targetSite e) k item
      exact ⟨info.1,info.2.1,info.2.2.1⟩

omit [Fintype R] in
theorem public_lane_vacant (dir : Bool) (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m) (j : Fin b)
    (absent : ¬∃e : Index,selected dir v r j e) :
    ∃bit,get dir v r k j=.fixed bit:=by
  cases dir with
  | false =>
    obtain ⟨bit,eqn⟩:=focus_missing ord (fun z=>(P.choose z,z.1)) sourceSite (fun _=>rfl) r v j (by
      intro e atRow atDigit
      exact absent ⟨e,congrArg Prod.snd atRow,congrArg Prod.fst atRow,atDigit⟩)
    exact ⟨bit,by simp only [publicTapLane,eqn,focusLane,Sum.elim_inl]⟩
  | true =>
    obtain ⟨bit,eqn⟩:=focus_missing ord (fun z=>(P.choose z,z.2.1)) targetSite (fun _=>rfl) r v j (by
      intro e atRow atDigit
      exact absent ⟨e,congrArg Prod.snd atRow,congrArg Prod.fst atRow,atDigit⟩)
    exact ⟨bit,by simp only [publicTapLane,eqn,focusLane,Sum.elim_inl]⟩

end
end Hierarchy.DescentResetLaneIssue

end OAI
