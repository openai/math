import OAI.Hierarchy.DescentOrdinaryRawPublicBlock
import OAI.Hierarchy.DescentNamedPublicEmission

namespace OAI
/-! An occupied public argument and the signed successor schedule identify the same
physical cable, chunk, and lane. -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.GadgetNetwork DescentKernelHistory
open DescentNetworkPartition DescentHostDirectory
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P I V T : Type} [Field F] [Fintype I] [DecidableEq T] {d p R Z : ℕ}
    {bits : P → ℕ} {W : MarkedWorld F d P bits} (B : BitDescription W)
    (G : PoweredGadget F) (pick : I × Fin 2 ↪ W.graph.Edge)
    (z : I → ℕ) (hz : ∀ i, 0 < z i) (fit : ∀ i j, W.graph.width (pick (i,j)) = z i * G.b)
    (room : ∀ i, z i ≤ Z) (pack : W.graph.Site → V) (prof : I → Profile G.C)
    (hp : 0 < p) (one : 1 ≤ R) (pin : ∀ a, p ∣ bits a) (sh : WorldShape p R B)
    (whole : ∀ i, p ∣ z i)
local notation "sel" => W.selected G pick z hz fit pack prof
local notation "sbit" => B.selected G pick z hz fit room pack prof
local notation "ss" => sh.selected hp one pin G pick z hz fit room pack prof whole
local notation "net" => physical W.graph pick (branchWidth G z prof)
local notation "grp" => newSite W.graph pick (bestLayout (branchWidth G z prof)) pack
local notation "oldBits" => physicalBits G W.toWorld pick z room prof B.recipe
local notation "oldShape" => physicalShape W B G pick z room prof hp sh.sites sh.edges pin whole
local notation "wireFits" => physical_multiple W G pick z prof sh.edges whole
variable (key : (W.selected G pick z hz fit pack prof).graph.Site → Key T) (flag : T → Bool) (k g : ℕ)
local notation "addr" => MarkedWorld.address sel key flag k g
local notation "reclaimed" => ↥(MarkedWorld.reclaimed sel key flag k g)
local notation "x₁" => fun _ : Merged W.graph pick (bestLayout (branchWidth G z prof)) pack => (0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : reclaimed => (0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun t : Merged W.graph pick (bestLayout (branchWidth G z prof)) pack => (by simp : ‖x₁ t‖ ≤ 1)
local notation "ok₂" => fun t : reclaimed => (by simp : ‖x₂ t‖ ≤ 1)
local notation "firstNet" => quotient net grp x₁ ok₁
local notation "firstBits" => quotientBits net grp x₁ ok₁ oldBits
local notation "lastWorld" => (sel).coalesced key flag k g
local notation "destShape" => (ss).coalesced key flag k g
local notation "destBits" => (sbit).coalesced key flag k g
local notation "firstShape" => quotientShape net grp x₁ ok₁ oldBits oldShape wireFits
local notation "lastShape" => quotientShape firstNet addr x₂ ok₂ firstBits firstShape (fun e => wireFits e.val)

set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false

local notation "nodeRaw" => coalescedPhysicalNode B G pick z hz fit room pack prof key flag k g
local notation "fromNode" => coalescedPhysicalOrigin B G pick z hz fit room pack prof key flag k g

open private physicalSourceArg physicalSourceArg_index mappedCableInput from OAI.Hierarchy.DescentOrdinaryRawPublicBlock
variable {Y : MarkedWorld F d P bits} {BY : BitDescription Y} {s : WorldShape p R BY}
local notation "bookArg" => physicalSourceArg B G pick z hz fit room pack prof hp one pin sh whole key flag k g

structure BookCableUse (book : SiteBooks hp s destShape) where
  node : NodeOrder.All BY
  arg : Fin (((s.sites node.1).recipe hp).arity node.2)
  cable : Incident net (fromNode (book.nodeAt hp node)).1
  chunk : ℕ
  fits : (chunk+1)*p ≤ (net).width cable.val
  survives : addr (grp ((net).src cable.val)) ≠ addr (grp ((net).dst cable.val))
  earlier : ((oldShape (fromNode (book.nodeAt hp node)).1).recipe hp).operand
    (fromNode (book.nodeAt hp node)).2 (bookArg (book.nodeAt hp node) (arg.cast ((book.atSite node.1).length node.2))) =
      .inl ⟨.inl cable,chunk,fits⟩

local notation "bookUses" => BookCableUse B G pick z hz fit room pack prof hp one pin sh whole key flag k g

theorem bookCableUse_origin (book : SiteBooks hp s destShape)
    (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (edge : Incident Y.graph x.1) (low : ℕ) (cap : (low+1)*p ≤ Y.graph.width edge.val)
    (hit : ((s.sites x.1).recipe hp).operand x.2 j = .inl ⟨.inl edge,low,cap⟩) :
    ∃ witness : bookUses book, witness.node = x ∧ HEq witness.arg j := by
  obtain ⟨e,chunk,wide,live,source⟩ := mappedCableInput B G pick z hz fit room pack prof hp one pin sh whole
    key flag k g book x j edge low cap hit
  exact ⟨⟨x,j,e,chunk,wide,live,source⟩,rfl,HEq.rfl⟩

theorem bookCableUse_number (book : SiteBooks hp s destShape) (witness : bookUses book)
    (y : NodeOrder.Global (N:=net) oldBits) (i : Fin (((oldShape y.1).recipe hp).arity y.2))
    (origin : y = fromNode (book.nodeAt hp witness.node)) (index : i.val = witness.arg.val) :
    (((oldShape y.1).recipe hp).operand y.2 i).elim (fun w => w.cableNumber net y.1) (fun _ => none) =
      some (witness.cable.val, witness.chunk) := by
  subst y
  have number := physicalSourceArg_index B G pick z hz fit room pack prof hp one pin sh whole
    key flag k g (book.nodeAt hp witness.node) (witness.arg.cast ((book.atSite _).length _))
  have eqn : i = bookArg (book.nodeAt hp witness.node) (witness.arg.cast ((book.atSite _).length _)) :=
    Fin.ext (index.trans number.symm)
  rw [eqn,witness.earlier]
  rfl

def BookCableOriginLaw (book : SiteBooks hp s destShape) : Prop :=
  ∀ (x : NodeOrder.All BY) (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (edge : Incident Y.graph x.1) (low : ℕ) (cap : (low+1)*p ≤ Y.graph.width edge.val)
    (_hit : ((s.sites x.1).recipe hp).operand x.2 j = .inl ⟨.inl edge,low,cap⟩),
  ∃ witness : bookUses book, witness.node = x ∧ HEq witness.arg j

theorem bookCableOriginLaw (book : SiteBooks hp s destShape) :
    BookCableOriginLaw B G pick z hz fit room pack prof hp one pin sh whole key flag k g book :=
  bookCableUse_origin B G pick z hz fit room pack prof hp one pin sh whole key flag k g book

end
end Hierarchy.DescentBundleHistory

namespace Hierarchy.DescentStageEdgeReceipt.OrdinaryModel
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
open private DescentBundleHistory.physicalSourceArg from OAI.Hierarchy.DescentOrdinaryRawPublicBlock
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows

variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {H : Type} [Fintype H] [DecidableEq H] {u ε : ℝ}
  (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
  (oldID : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (model : OrdinaryModel he T c H)
  (arch : Archive W) (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "prior" => sh.selected hp one pin G (r).pick uni pos (r).fit room (r).pack prof whole
local notation "normal" => model.named he T c oldID
local notation "valid" => (show Normalize.CutsEqual T.z normal from ⟨rfl,trivial⟩)
local notation "after" => WorldShape.follow hp T.unitPos unit normal valid prior
local notation "b" => model.chart
local notation "addr" => MarkedWorld.address sel ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "bk" => model.publicBooks he T c oldID hp prior unit
local notation "group" => GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
attribute [local instance] rawPublicBlockScannedSites
local notation "loc" => addr ∘ group
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole



local notation "ed" => model.edgeMap he T c oldID
local notation "coarse₀" => (sel).coalesced ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "reps" => MarkedWorld.repetitions W G (r).pick uni pos (r).fit (r).pack prof ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) T.z
local notation "actual" => (bk).nodeAt hp
local notation "rawOrigin" => coalescedPhysicalOrigin arch.bit G (r).pick uni pos (r).fit room (r).pack prof
  ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "src₀" => rawOrigin ∘ actual
local notation "physicalArg" => DescentBundleHistory.physicalSourceArg arch.bit G (r).pick uni pos (r).fit room (r).pack prof
  hp one pin sh whole ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "rgraph" => (normal).result.graph

local notation "base" => physicalBits G W.toWorld (r).pick uni room prof arch.bit.recipe
local notation "x₁" => fun _ : (sel).graph.Site => (0 : EuclideanSpace ℝ (Fin d))
local notation "C" => ↥(MarkedWorld.reclaimed sel ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ))
local notation "x₂" => fun _ : C => (0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun x : (sel).graph.Site => (by simp : ‖x₁ x‖ ≤ 1)
local notation "ok₂" => fun x : C => (by simp : ‖x₂ x‖ ≤ 1)
local notation "wireFits" => physical_multiple W G (r).pick uni prof sh.edges whole
local notation "pre" => (prior).coalesced ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)

open DescentOrdinaryParentBlocks DescentOrdinaryWindowFields DescentOrdinarySiblingSerial DescentSIMDLookup DescentSixParty.StarKeys DescentPacking
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage date : ℕ} {price error : ℝ}
    (A : GroupStage (model.named he T c oldID).result G price error J V stage) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S date) (tickSize : A.z*G.b=T.z)
local notation "pair" => PairRAM.globalNumberBy W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap
  (DescentPacking.originalId (ScanColonies he T))
local notation "parent" => blocks (J:=J) (V:=V) (stage:=stage) (price:=price) (ε:=error) W G oldID pair (r).pick uni pos (r).fit (r).pack prof ((b).key he T c) (b).hub T.k
  (gainExponent 20 T.Δ) T.z model.old model.used (fun _=>dvd_refl T.z) model.site A T.unitPos
local notation "issue" => signedEmission (J:=J) (V:=V) (stage:=stage) (price:=price) (ε:=error) W G oldID pair (r).pick uni pos (r).fit (r).pack prof ((b).key he T c) (b).hub T.k
  (gainExponent 20 T.Δ) T.z model.old model.used (fun _=>dvd_refl T.z) model.site A T.unitPos
local notation "numberedOperand" => emittedOperandNumber (J:=J) (V:=V) (age:=stage) (price:=price) (ε:=error)
  W G oldID pair (r).pick uni pos (r).fit (r).pack prof ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
  T.z model.old model.used (fun _ => dvd_refl T.z) model.site A T.unitPos (unit:=p)
set_option maxHeartbeats 3500000 in
include S ready tickSize in
theorem raw_emitted_operand (x : NodeOrder.All ((arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof).follow normal))
    (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (e : Incident M (src₀ x).1) (chunk : ℕ) (fits : (chunk+1)*p≤(M).width e.val)
    (pass : loc ((M).src e.val)≠loc ((M).dst e.val))
    (read : ((baseShape (src₀ x).1).recipe hp).operand (src₀ x).2 (physicalArg (actual x) (j.cast (((bk).atSite x.1).length x.2)))=.inl ⟨.inl e,chunk,fits⟩) :
    let root : (coarse₀).graph.Edge := ⟨⟨e.val, fun h => pass (congrArg addr h)⟩,pass⟩
    numberedOperand root chunk
      (fun w : BlockRef p (boundaryWidth rgraph x.1) => (((after).sites x.1).recipe hp).operand x.2 j = .inl w)
      (fun w => w.cableNumber rgraph x.1) := by
  intro root
  let observed : BlockRef p (boundaryWidth rgraph x.1) → Prop := fun w => (((after).sites x.1).recipe hp).operand x.2 j = .inl w
  let number : BlockRef p (boundaryWidth rgraph x.1) → Option ((rgraph).Edge × ℕ) := fun w => w.cableNumber rgraph x.1
  have rule := emittedNumber_of_publicBlock (I:=(r).pairs) (H:=H) (J:=J) (V:=V) (age:=stage) (price:=price) (ε:=error)
    (Q:=BlockRef p (boundaryWidth rgraph x.1)) (unit:=p) W G oldID pair (r).pick uni pos (r).fit (r).pack prof
    ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) T.z model.old model.used (fun _ => dvd_refl T.z) model.site A
    hp T.unitPos unit S ready tickSize root chunk fits observed number
  have published := raw_public_block he T c oldID model arch hp one pin sh unit x j e chunk fits pass read
  exact rule published

private abbrev nodeArgument {W' : MarkedWorld F d P bits} {B' : BitDescription W'}
    (positive : 0 < p) (shape : WorldShape p R B') (x : NodeOrder.All B') :=
  Fin (((shape.sites x.1).recipe positive).arity x.2)

private abbrev nodeRead {W' : MarkedWorld F d P bits} {B' : BitDescription W'}
    (positive : 0 < p) (shape : WorldShape p R B') (x : NodeOrder.All B') (j : nodeArgument positive shape x) :=
  ((shape.sites x.1).recipe positive).operand x.2 j

abbrev PublicNode := NodeOrder.All ((arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof).follow normal)
abbrev PublicArg := nodeArgument hp after
abbrev publicOperand := nodeRead hp after

abbrev PublicUse := BookCableUse arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
  ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) bk
variable (use : PublicUse he T c oldID model arch hp one pin sh unit)
def PublicUse.parent : (coarse₀).graph.Edge := ⟨⟨use.cable.val,fun h => use.survives (congrArg addr h)⟩,use.survives⟩
def PublicUse.finalOperand := nodeRead hp after use.node use.arg

theorem PublicUse.raw_root :
    NodeOrder.physicalNames arch.bit G (r).pick uni room prof (src₀ use.node)=
      NodeOrder.selectedNames arch.bit G (r).pick uni pos (r).fit room (r).pack prof
        (NodeOrder.followNames normal (arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof) use.node) :=by
  rcases use with ⟨⟨v,a⟩,j,e,lo,room_,carried,prior_⟩
  rfl

theorem PublicUse.raw_number (y : NodeOrder.Global base) (k : Fin (((baseShape y.1).recipe hp).arity y.2))
    (same : NodeOrder.physicalNames arch.bit G (r).pick uni room prof y=
      NodeOrder.selectedNames arch.bit G (r).pick uni pos (r).fit room (r).pack prof
        (NodeOrder.followNames normal (arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof) use.node))
    (index : k.val=use.arg.val) :
    (((baseShape y.1).recipe hp).operand y.2 k).elim (fun w=>w.cableNumber M y.1) (fun _=>none)=
      some (use.cable.val,use.chunk) :=by
  have origin := (NodeOrder.physicalNames arch.bit G (r).pick uni room prof).injective
    (same.trans (PublicUse.raw_root he T c oldID model arch hp one pin sh unit use).symm)
  exact bookCableUse_number arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) bk use y k origin index

theorem public_origin : BookCableOriginLaw arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) bk :=
  bookCableOriginLaw arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) bk


local notation "emittedUseProof" => raw_emitted_operand he T c oldID model arch hp one pin sh unit A S ready tickSize
  use.node use.arg use.cable use.chunk use.fits use.survives use.earlier

set_option maxHeartbeats 3500000 in
include S ready tickSize in
/-- The signed edge and lane for the surviving cable read at this public argument. -/
theorem PublicUse.emitted : type_of% emittedUseProof := emittedUseProof

end
end Hierarchy.DescentStageEdgeReceipt.OrdinaryModel

end OAI
