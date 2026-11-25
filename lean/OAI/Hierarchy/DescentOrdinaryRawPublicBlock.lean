import OAI.Hierarchy.DescentOrdinaryModelPublicBooks
import OAI.Hierarchy.DescentQuotientPublicNumber
import OAI.Hierarchy.DescentReachedSourceOperand

namespace OAI
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

private def physicalCableIndex (node : NodeOrder.All destBits)
    (j : Fin ((((destShape).sites node.1).recipe hp).arity node.2)) :
    Fin (((lastShape (nodeRaw node).1).recipe hp).arity (nodeRaw node).2) := by
  dsimp only [coalescedPhysicalNode, WorldShape.coalesced, WorldShape.selected, Shape.coalesced, Shape.selected,
    BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced, MarkedWorld.selected, recorded, recordedBits] at j ⊢
  exact j

local notation "indexRaw" => physicalCableIndex B G pick z hz fit room pack prof hp one pin sh whole key flag k g

private def physicalSourceArg (node : NodeOrder.All destBits)
    (j : Fin ((((destShape).sites node.1).recipe hp).arity node.2)) :
    Fin (((oldShape (fromNode node).1).recipe hp).arity (fromNode node).2) :=
  sourceArg net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂ (nodeRaw node) (indexRaw node j)

local notation "srcIndex" => physicalSourceArg B G pick z hz fit room pack prof hp one pin sh whole key flag k g

private theorem coalescedSourceCable (node : NodeOrder.All destBits)
    (j : Fin ((((destShape).sites node.1).recipe hp).arity node.2))
    (e : Incident net (fromNode node).1) (chunk : ℕ) (lengthFits : (chunk+1)*p≤(net).width e.val)
    (pass : addr (grp ((net).src e.val)) ≠ addr (grp ((net).dst e.val)))
    (read : ((oldShape (fromNode node).1).recipe hp).operand (fromNode node).2 (srcIndex node j) =
      .inl ⟨.inl e,chunk,lengthFits⟩) :
    ∃ u : Incident (lastWorld).graph node.1, ∃ wide : (chunk+1)*p ≤ (lastWorld).graph.width u.val,
      u.val.val.val=e.val ∧ (((destShape).sites node.1).recipe hp).operand node.2 j = .inl ⟨.inl u,chunk,wide⟩ := by
  obtain ⟨cable,wide,same,hit⟩ := source_cable net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂
    (nodeRaw node) (indexRaw node j) e chunk lengthFits pass read
  exact ⟨cable,wide,same,hit⟩
variable {Y : MarkedWorld F d P bits} {BY : BitDescription Y} {s : WorldShape p R BY}

private theorem physicalCableOrdinal (node : NodeOrder.All destBits)
    (j : Fin ((((destShape).sites node.1).recipe hp).arity node.2)) : (indexRaw node j).val = j.val := rfl

private theorem physicalSourceArg_index (node : NodeOrder.All destBits)
    (j : Fin ((((destShape).sites node.1).recipe hp).arity node.2)) : (srcIndex node j).val = j.val := by
  unfold physicalSourceArg
  have chosen := source_arg_read net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂ (nodeRaw node) (indexRaw node j)
  exact chosen.trans (physicalCableOrdinal B G pick z hz fit room pack prof hp one pin sh whole key flag k g node j)

private theorem coalescedCableInput (node : NodeOrder.All destBits)
    (j : Fin ((((destShape).sites node.1).recipe hp).arity node.2))
    (u : Incident (lastWorld).graph node.1) (k : ℕ) (wide : (k+1)*p ≤ (lastWorld).graph.width u.val)
    (hit : (((destShape).sites node.1).recipe hp).operand node.2 j = .inl ⟨.inl u,k,wide⟩) :
    ∃ e : Incident net (fromNode node).1, ∃ chunk : ℕ, ∃ fits : (chunk+1)*p ≤ (net).width e.val,
      addr (grp ((net).src e.val)) ≠ addr (grp ((net).dst e.val)) ∧
      ((oldShape (fromNode node).1).recipe hp).operand (fromNode node).2 (srcIndex node j) = .inl ⟨.inl e,chunk,fits⟩ := by
  let physicalEdge : Incident (quotient firstNet addr x₂ ok₂) (nodeRaw node).1 := by
    dsimp only [coalescedPhysicalNode, MarkedWorld.coalesced, MarkedWorld.selected, recorded] at u ⊢
    exact u
  have physicalWidth : (k+1)*p ≤ (quotient firstNet addr x₂ ok₂).width physicalEdge.val := by
    dsimp only [physicalEdge, coalescedPhysicalNode, MarkedWorld.coalesced, MarkedWorld.selected, recorded] at wide ⊢
    exact wide
  have physicalHit : ((lastShape (nodeRaw node).1).recipe hp).operand (nodeRaw node).2 (indexRaw node j) = .inl ⟨.inl physicalEdge,k,physicalWidth⟩ := by
    dsimp only [physicalEdge, coalescedPhysicalNode, physicalCableIndex, WorldShape.coalesced, WorldShape.selected, Shape.coalesced, Shape.selected,
      BitDescription.coalesced, BitDescription.selected, MarkedWorld.coalesced, MarkedWorld.selected, recorded, recordedBits] at hit ⊢
    exact hit
  obtain ⟨wire,chunk,bounded,survives,read⟩ := source_cable_origin net grp x₁ ok₁ oldBits oldShape wireFits hp addr x₂ ok₂ (nodeRaw node) (indexRaw node j) physicalEdge k physicalWidth physicalHit
  exact ⟨wire,chunk,bounded,survives,read⟩

private theorem mappedCableInput (book : SiteBooks hp s destShape) (x : NodeOrder.All BY)
    (j : Fin (((s.sites x.1).recipe hp).arity x.2)) (e : Incident Y.graph x.1) (low : ℕ)
    (wide : (low+1)*p ≤ Y.graph.width e.val)
    (hit : ((s.sites x.1).recipe hp).operand x.2 j = .inl ⟨.inl e,low,wide⟩) :
    ∃ wire : Incident net (fromNode (book.nodeAt hp x)).1, ∃ chunk : ℕ, ∃ fits : (chunk+1)*p ≤ (net).width wire.val,
      addr (grp ((net).src wire.val)) ≠ addr (grp ((net).dst wire.val)) ∧
      ((oldShape (fromNode (book.nodeAt hp x)).1).recipe hp).operand (fromNode (book.nodeAt hp x)).2
        (srcIndex (book.nodeAt hp x) (j.cast ((book.atSite x.1).length x.2))) = .inl ⟨.inl wire,chunk,fits⟩ := by
  obtain ⟨first,original,visible⟩ := WordBook.public_origin _ _ (book.atSite x.1) x.2 j _ hit
  rcases first with ⟨wire|connector,n,cableRoom⟩
  · exact coalescedCableInput B G pick z hz fit room pack prof hp one pin sh whole key flag k g
      (book.nodeAt hp x) (j.cast ((book.atSite x.1).length x.2)) wire n cableRoom original
  · have payload := congrArg (BlockRef.pinPayload Y.graph x.1) visible
    rw [book.pinPayload] at payload
    contradiction

private theorem mappedSourceCable (book : SiteBooks hp s destShape) (x : NodeOrder.All BY)
    (j : Fin (((s.sites x.1).recipe hp).arity x.2))
    (e : Incident net (fromNode (book.nodeAt hp x)).1) (chunk : ℕ)
    (bounded : (chunk+1)*p≤(net).width e.val)
    (pass : addr (grp ((net).src e.val)) ≠ addr (grp ((net).dst e.val)))
    (read : ((oldShape (fromNode (book.nodeAt hp x)).1).recipe hp).operand
      (fromNode (book.nodeAt hp x)).2 (srcIndex (book.nodeAt hp x) (j.cast ((book.atSite x.1).length x.2))) =
      .inl ⟨.inl e,chunk,bounded⟩)
    (records : (lastWorld).graph.Edge → BlockRef p (boundaryWidth Y.graph x.1) → Prop)
    (recorded : ∀ (u : Incident (lastWorld).graph (book.home x.1))
      (w : (chunk+1)*p≤(lastWorld).graph.width u.val),
      records u.val ((book.atSite x.1).publicWord ⟨.inl u,chunk,w⟩)) :
    let root : (lastWorld).graph.Edge := ⟨⟨e.val,fun h=>pass (congrArg addr h)⟩,pass⟩
    ∃ w : BlockRef p (boundaryWidth Y.graph x.1), ((s.sites x.1).recipe hp).operand x.2 j=.inl w ∧
      records root w := by
  intro root
  obtain ⟨carrier,wide,idEq,hit⟩ := coalescedSourceCable B G pick z hz fit room pack prof hp one pin sh
    whole key flag k g (book.nodeAt hp x) (j.cast ((book.atSite x.1).length x.2)) e chunk bounded pass read
  have same : carrier.val = root := Subtype.ext (Subtype.ext idEq)
  let word : BlockRef p (boundaryWidth (lastWorld).graph (book.home x.1)) := ⟨.inl carrier,chunk,wide⟩
  exact ⟨(book.atSite x.1).publicWord word,(book.atSite x.1).publicHit x.2 j word hit,
    (congrArg (fun edge => records edge ((book.atSite x.1).publicWord word)) same).mp (recorded carrier wide)⟩

end
end Hierarchy.DescentBundleHistory

/-! Resolve the public wire read at a genuine final argument from the old scalar
operand, through both contractions, the real cut, and the final source-ordered tape. -/
namespace Hierarchy.DescentStageEdgeReceipt.OrdinaryModel
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
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
local instance rawPublicBlockScannedSites : Fintype (Merged W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack) :=
  mergedFinite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
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
local notation "arg₀" => physicalSourceArg arch.bit G (r).pick uni pos (r).fit room (r).pack prof
  hp one pin sh whole ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "rgraph" => (normal).result.graph

private theorem classify_by_membership {P : Prop} [Decidable P] {yes : P → Prop} {no : ¬P → Prop}
    (left : ∀ h,yes h) (right : ∀ h,no h) : dite P yes no := by
  split
  · exact left _
  · exact right _

theorem raw_public_block (x : NodeOrder.All ((arch.bit.selected G (r).pick uni pos (r).fit room (r).pack prof).follow normal))
    (j : Fin ((((after).sites x.1).recipe hp).arity x.2))
    (e : Incident M (src₀ x).1) (chunk : ℕ) (fits : (chunk+1)*p≤(M).width e.val)
    (pass : loc ((M).src e.val)≠loc ((M).dst e.val))
    (read : ((baseShape (src₀ x).1).recipe hp).operand (src₀ x).2 (arg₀ (actual x) (j.cast (((bk).atSite x.1).length x.2)))=.inl ⟨.inl e,chunk,fits⟩) :
    let root : (coarse₀).graph.Edge := ⟨⟨e.val,fun h=>pass (congrArg addr h)⟩,pass⟩
    ∃w : BlockRef p (boundaryWidth rgraph x.1),
      (((after).sites x.1).recipe hp).operand x.2 j=.inl w ∧
      (if core : root∈(coarse₀).core then
        ∃cut : Fin (reps root), cut.val=chunk/(T.z/p) ∧
          w.cableNumber rgraph x.1=some (ed (.inr ⟨⟨root,core⟩,cut⟩),chunk%(T.z/p))
       else w.cableNumber rgraph x.1=some (ed (.inl ⟨root,core⟩),chunk)) := by
  let records (root : (coarse₀).graph.Edge) (w : BlockRef p (boundaryWidth rgraph x.1)) : Prop :=
    if core : root∈(coarse₀).core then
      ∃ cut : Fin (reps root), cut.val=chunk/(T.z/p) ∧
        w.cableNumber rgraph x.1=some (ed (.inr ⟨⟨root,core⟩,cut⟩),chunk%(T.z/p))
    else w.cableNumber rgraph x.1=some (ed (.inl ⟨root,core⟩),chunk)
  have recorded (u : Incident (coarse₀).graph ((bk).home x.1))
      (wide : (chunk+1)*p≤(coarse₀).graph.width u.val) :
      records u.val (((bk).atSite x.1).publicWord ⟨.inl u,chunk,wide⟩) := by
    exact classify_by_membership
      (fun mark => model.paid_public he T c oldID hp prior unit x.1 u chunk wide mark)
      (fun mark => model.unmarked_public he T c oldID hp prior unit x.1 u chunk wide mark)
  exact mappedSourceCable arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) bk x j e chunk fits pass read records recorded

end
end Hierarchy.DescentStageEdgeReceipt.OrdinaryModel

end OAI
