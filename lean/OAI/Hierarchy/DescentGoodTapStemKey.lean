import OAI.Hierarchy.DescentClosedResetSlotCount
import OAI.Hierarchy.DescentResetOriginalOperandSite
import OAI.Hierarchy.DescentCalendarPublicSocketField
import OAI.Hierarchy.DescentResetTrunkOperandPrefix
import OAI.Hierarchy.DescentPublicOperandPhysicalPorts

namespace OAI
/-! The incoming side of a live rotor public tap reads the chronologically
selected original stem and the residual block within that original cable. -/
namespace Hierarchy.DescentOrderedWords
open scoped Classical BigOperators
noncomputable section
variable {I : Type*} [Fintype I] {N p width units : ℕ} (key : I↪Fin N)
theorem address_pword (hp : 0<p) (positive : 0<units) (unitSize : width=units*p)
    (word : ℕ) (pointer : Fin (∑ _ : I,width)) (low : pointer.val=word*p)
    (item : I) (rank : (before key item).card=word/units) :
    ((address key (fun _ : I=>width)).symm pointer).1=item ∧
      ((address key (fun _ : I=>width)).symm pointer).2.val/p=word%units :=by
  have bounded : (word%units)*p<width:=by
    rw [unitSize]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ positive) hp
  let localBit : Fin width:=⟨(word%units)*p,bounded⟩
  have native : address key (fun _ : I=>width) ⟨item,localBit⟩=pointer:=by
    apply Fin.ext
    rw [address_val,low]
    have base : offset key (fun _ : I=>width) item=(word/units)*width:=by simp [offset,rank]
    change offset key (fun _ : I=>width) item+(word%units)*p=word*p
    rw [base,unitSize,←Nat.mul_assoc,←Nat.add_mul,Nat.mul_comm (word/units) units,Nat.div_add_mod]
  rw [←native,Equiv.symm_apply_apply]
  exact ⟨rfl,Nat.mul_div_cancel _ hp⟩
end
end Hierarchy.DescentOrderedWords

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "world" => B.reset.orderedOrdinary B.terminals birth
local notation "cnt" => fun e=>(coarse).graph.width e/B.reset.unit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite
local notation "edgeName" => DescentPhysicalOrder.rename sparse



open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "raw_" => W.granular B.count (z*G.b) B.fit
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation:max "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
local notation:max "where_" x:arg => resetOrigin B hp whole a x
local notation "dev_" => B.reset.laneShape birth unit p hp splitEq
local notation "loc_" => fun e : (raw_).graph.Edge=>B.terminals.home ((raw_).graph.dst e)

open DescentLaneGates
local notation:max "prog_" v:arg => B.reset.laneProgram birth unit p hp splitEq v
local notation:max "words_" v:arg => fun t : Boundary B.reset.bank v=>boundaryWidth B.reset.bank v t/p
local notation:max "fit_" v:arg => B.reset.laneWidth_eq unit p splitEq v

open DescentOrderedWords DescentOrderedReset
local notation "width_" => B.reset.unit
local notation:max "rank_" socket:arg => DescentOrderedReset.fibreKey birth (B.reset.placement.input (socket).val.1) (socket).val.2
local notation:max "cells_" socket:arg => Fibre (B.reset.placement.input (socket).val.1) (socket).val.2
local notation:max "weights_" socket:arg => fun _ : cells_ socket=>width_

/-- Inverting the ordered socket at the first bit of the p-block agrees
with the donor selected by the actual earlier-count rank. -/
theorem good_tap_stem_route (v : B.reset.bank.Site) (socket : Attached B.reset.bank v) (word : ℕ)
    (fit : (word+1)*p≤boundaryWidth B.reset.bank v (.inr socket))
    (item : cells_ socket) (positive : 0<unit) (size : width_=unit*p)
    (rank : (DescentOrderedWords.before (rank_ socket) item).card=word/unit) :
    deviceRoute B hp v ⟨.inr socket,word,fit⟩=(stemParent B (socket.val.1,item.val),word%unit) :=by
  let ref : BlockRef p (boundaryWidth B.reset.bank v):=⟨.inr socket,word,fit⟩
  let picked := (address (rank_ socket) (weights_ socket)).symm (ref.atBit ⟨0,hp⟩).2
  have aligned (fnt : Fintype (cells_ socket)) :
      (@DescentOrderedWords.before _ fnt _ (rank_ socket) item).card=word/unit := by
    exact (congrArg (fun use : Fintype (cells_ socket) =>
      (@DescentOrderedWords.before _ use _ (rank_ socket) item).card) (Subsingleton.elim fnt _)).trans rank
  have chosen := address_pword (rank_ socket) hp positive size word (ref.atBit ⟨0,hp⟩).2
    (by simp [ref,BlockRef.atBit]) item (aligned _)
  change (stemParent B (socket.val.1,picked.1.val),picked.2.val/p)=_
  exact Prod.ext (congrArg (fun t : cells_ socket=>stemParent B (socket.val.1,t.val)) chosen.1) chosen.2

/-- A normalized occupied tap input refers to the actual stem at its
destination. The named bank socket is the one on the original device node. -/
theorem good_tap_stem_key (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (prog_ v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩)) (j : ℕ)
    (socket : Attached B.reset.bank v) (word : ℕ) (fit : (word+1)*p≤boundaryWidth B.reset.bank v (.inr socket))
    (read : ((dev_ v).keys u)[j]?=some (.inl ⟨.inr socket,word,fit⟩))
    (item : cells_ socket) (rank : (DescentOrderedWords.before (rank_ socket) item).card=word/unit) :
    keyCable installed (middle_ x) j=some (stemParent B (socket.val.1,item.val),word%unit) ∧
      (coarse).graph.dst (stemParent B (socket.val.1,item.val))=(hop).symm x.1 :=by
  have positive : 0<unit := Nat.div_pos (Nat.le_of_dvd pos whole) hp
  refine ⟨(device_route_key B hp one pos whole wide a sh x v u origin j _ read).trans
    (congrArg some (good_tap_stem_route B hp v socket word fit item positive splitEq rank)),?_⟩
  exact (device_socket_original_site B hp whole a x v u origin socket item.val item.property).symm

open DescentResetOperandComponents
local notation:max "pubCfg" field:arg query:arg lanes:arg batches:arg nodes:arg args:arg grain:arg => publicOperandConfig B field query lanes batches unit nodes args grain
/-- The numerical stem reference of the chosen donor is also the public
socket whose face and residual word the native operand header records. -/
theorem good_tap_stem_socket_key {field query lanes batches nodes args grain : ℕ}
    (y : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (prog_ v).Node) (origin : where_ y=.inr (.inr ⟨v,u⟩)) (j : ℕ)
    (socket : Attached B.reset.bank v) (word : ℕ) (fit : (word+1)*p≤boundaryWidth B.reset.bank v (.inr socket))
    (read : ((dev_ v).keys u)[j]?=some (.inl ⟨.inr socket,word,fit⟩))
    (item : cells_ socket) (rank : (DescentOrderedWords.before (rank_ socket) item).card=word/unit)
    (row : (pubCfg field query lanes batches nodes args grain).Data B.reset.n) :
    let lower:=beforeStem B item.val
    let home:=(blocks B).dst (stemParent B (socket.val.1,item.val))
    let number:=(pubCfg field query lanes batches nodes args grain).oldConfig.stemAt socket.val.1 cap.placement.cap
      ((pubCfg field query lanes batches nodes args grain).oldItem row socket.val.1 (oldRotorCell B socket.val.1 lower))
    ∃out : PublicSocket B home unit (word%unit) false number,
      keyCable installed (middle_ y) j=some (out.face.val.1,word%unit) ∧
      (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1 :=by
  intro lower home number
  have chosen:=good_tap_stem_key B hp one pos whole wide a sh y v u origin j socket word fit read item rank
  have restored:oldOfGrain B lower=item.val:=
    (Equiv.sigmaCongrRight fun e=>finCongr (congrFun B.count_eq e)).symm_apply_apply _
  have positive : 0<unit := Nat.div_pos (Nat.le_of_dvd pos whole) hp
  let out:=reached_stem_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=unit) (nodes:=nodes) (args:=args) (grain:=grain) B socket.val.1 row lower (word%unit) (Nat.mod_lt _ positive)
  have actual : ∃skt : PublicSocket B ((blocks B).dst (stemParent B (socket.val.1,oldOfGrain B lower)))
      unit (word%unit) false number, keyCable installed (middle_ y) j=some (skt.face.val.1,word%unit) ∧
      (if skt.face.val.2 then (coarse).graph.dst skt.face.val.1 else (coarse).graph.src skt.face.val.1)=(hop).symm y.1 :=by
    refine ⟨out,?_,?_⟩
    · change keyCable installed (middle_ y) j=some (stemParent B (socket.val.1,oldOfGrain B lower),word%unit)
      simpa only [restored] using chosen.1
    · change (coarse).graph.dst (stemParent B (socket.val.1,oldOfGrain B lower))=(hop).symm y.1
      simpa only [restored] using chosen.2
  let hasSocket := fun h₀ => ∃ skt : PublicSocket B h₀ unit (word%unit) false number,
    keyCable installed (middle_ y) j=some (skt.face.val.1,word%unit) ∧
    (if skt.face.val.2 then (coarse).graph.dst skt.face.val.1 else (coarse).graph.src skt.face.val.1)=(hop).symm y.1
  have homeEq := congrArg (fun edge => (blocks B).dst (stemParent B (socket.val.1,edge))) restored
  exact Eq.mp (congrArg hasSocket homeEq) actual

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
