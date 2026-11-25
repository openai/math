import OAI.Hierarchy.DescentOldBoundaryCablePort
import OAI.Hierarchy.DescentOrdinaryRawOperandOrigin

namespace OAI
/-! The true earlier operand, its unclipped p-word and the original matcher's exact cable row. -/
namespace Hierarchy.DescentOrdinaryRawOperandOrigin
open Computability.BorderVNP.Crossing DescentNetworkPartition DescentSixParty DescentKernelHistory DescentBundleHistory GadgetNetwork
open DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P I : Type} [Field F] [Fintype I] {d p Z:ℕ} {bits:P→ℕ}
    {W:MarkedWorld F d P bits} (B:BitDescription W) (G:PoweredGadget F)
    (pick:I×Fin 2↪W.graph.Edge) (z:I→ℕ) (room:∀i,z i≤Z) (prof:I→Profile G.C)
    (hp:0<p) (old:∀v,Shape p (B.recipe v))
    (edges:∀e,p∣W.graph.width e) (pins:∀x,p∣bits x) (units:∀i,p∣z i)
local notation "N" => W.graph
local notation "raw" => physical N pick (branchWidth G z prof)
local notation "layout" => physicalShape W B G pick z room prof hp old edges pins units
local notation "names" => NodeOrder.physicalNames B G pick z room prof

/-- A retained raw cable word has the same piece ordinal at its actual old incidence.
The last equation identifies the edge produced by the actual gadget's boundary map. -/
theorem real_old_wire (v:(raw).Site) (node:((layout v).recipe hp).Node)
    (j:Fin (((layout v).recipe hp).arity node)) (donor:NodeOrder.All B)
    (origin:names ⟨v,node⟩=.inl donor) (wire:Incident raw v) (piece:ℕ)
    (fits:(piece+1)*p≤(raw).width wire.val)
    (read:((layout v).recipe hp).operand node j=.inl ⟨.inl wire,piece,fits⟩) :
    ∃(s:Fin (((old donor.1).recipe hp).arity donor.2)) (q:Incident N donor.1)
        (oldFits:(piece+1)*p≤(N).width q.val), s.val=j.val ∧
      ((old donor.1).recipe hp).operand donor.2 s=.inl ⟨.inl q,piece,oldFits⟩ ∧
      projectedWire raw (.inl donor.1) (oldBoundary N pick (branchWidth G z prof) donor.1 (.inl q))=some wire.val :=by
  cases v with
  | inr i=>cases origin
  | inl v=>
    have ident:(⟨v,node⟩:NodeOrder.All B)=donor:=Sum.inl.inj origin
    subst donor
    let s:=previousIndex W B G pick z room prof hp old edges pins units v node j
    have routed:=((raw_old_read W B G pick z room prof hp old edges pins units v node j).2).symm.trans read
    change (((old v).recipe hp).operand node s).map (carriedMap W G pick z prof v).map id=
      .inl ⟨.inl wire,piece,fits⟩ at routed
    cases previous:((old v).recipe hp).operand node s with
    | inr h=>simp [previous] at routed
    | inl b=>
      obtain ⟨q|a,k,width⟩:=b
      · rw [previous,Sum.map_inl] at routed
        have equal:=Sum.inl.inj routed
        have same:k=piece:=congrArg BlockRef.block equal
        subst k
        exact ⟨s,q,width,rfl,previous,congrArg (fun b:BlockRef p (boundaryWidth raw (.inl v))=>projectedWire raw (.inl v) (b).port) equal⟩
      · rw [previous,Sum.map_inl] at routed
        have portEq:=congrArg BlockRef.port (Sum.inl.inj routed)
        contradiction

end
end Hierarchy.DescentOrdinaryRawOperandOrigin

namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D z' D' priorWire hist : ℕ}
    {cap : Reached W G q ε S k i z D priorWire hist}
    {he : 0≤ε} {c : (cap.placement.stage.result he).Choice}
    {n : Normalize ((cap.placement.stage.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' priorWire hist}
    (ticket : OrdinaryLink cap he cap.placement.stage c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣cap.placement.stage.z)
local notation "T" => cap.placement.stage
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>(T).z
local notation "pos" => fun _ : (r).pairs=>(T).unitPos
local notation "room" => fun _ : (r).pairs=>le_refl (T).z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "prior" => sh.selected hp one pin G r.pick uni pos r.fit room r.pack prof whole
local notation "cut" => (ticket.quantum.symm ▸ ticket.cuts)
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "b" => privateChart ticket arch hp one pin sh unit
local notation "addr" => MarkedWorld.address sel (b.key he T c) b.hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel (b.key he T c) b.hub T.k (gainExponent 20 T.Δ))
local notation "pre" => prior.coalesced (b.key he T c) b.hub T.k (gainExponent 20 T.Δ)
local notation "bk" => privateBooks ticket arch hp one pin sh unit
local notation "group" => GadgetNetwork.newSite W.graph r.pick (bestLayout (branchWidth G uni prof)) r.pack
local notation "loc" => addr ∘ group
local notation "x₁" => fun _ : sel.graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun x : sel.graph.Site=> (by simp : ‖x₁ x‖≤1)
local notation "ok₂" => fun x : C=> (by simp : ‖x₂ x‖≤1)
local notation "M" => rawGraph he T c
local notation "base" => physicalBits G W.toWorld r.pick uni room prof arch.bit.recipe
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "wireFits" => physical_multiple W G r.pick uni prof sh.edges whole
local notation "quot" => quotient M group x₁ ok₁
local notation "r₁" => quotientBits M group x₁ ok₁ base
local notation "q₂" => quotient quot addr x₂ ok₂
local notation "r₂" => quotientBits quot addr x₂ ok₂ r₁
local notation "firstRead" v => nextArg M group x₁ ok₁ base hp v
local notation "secondRead" v => nextArg quot addr x₂ ok₂ r₁ hp (group v)
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation "source" x:arg => (names).symm (roots ticket arch x)
local notation "values" => (Σ t,BlockRef p (boundaryWidth q₂ t)⊕Private (r₂ t) p)

open DescentPacking.PackedMatch.Local.Stage
local notation "args_" x:arg => (((after).sites (x:NodeOrder.All next).1).recipe hp).arity (x).2
local notation "input_" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2
    (sourceIndex ticket arch hp one pin sh unit x j)
local notation "anchor_" e:arg => DescentCableDonorNames.anchor (r).pick (e).val
local notation "live" => DescentRawCablePanel.Live cap.placement (r).pick
local notation "parent_" e:arg => (⟨anchor_ e,(e:live).property⟩:DescentSharedCableNames.Stage.Positive cap.placement)

private theorem positive_grains_of_word {width count size piece p : ℕ} (hp : 0 < p)
    (within : (piece+1)*p ≤ width) (total : width = count*size) : 0 < count := by
  by_contra! zero
  rw [Nat.eq_zero_of_le_zero zero, Nat.zero_mul] at total
  exact (Nat.ne_of_gt ((Nat.mul_pos (Nat.zero_lt_succ piece) hp).trans_le within)) total

/-- The original operand and matcher witness, including its source occurrence and positive cable. -/
private abbrev OriginalOldCableStatement : Prop :=
  ∀ (x:NodeOrder.All next) (j:Fin (args_ x)) (saved:NodeOrder.All arch.bit)
    (_:roots ticket arch x=.inl saved) (wire:Incident (M) (source x).1) (piece:ℕ)
    (fits:(piece+1)*p≤(M).width wire.val) (_:input_ x j=.inl ⟨.inl wire,piece,fits⟩),
    let alive:=DescentPrivateRawLabels.parent_positive cap.placement S cap.valid (r).pick uni pos (r).fit prof hp
        (⟨wire.val,piece,((Nat.le_div_iff_mul_le hp).mpr fits)⟩:WireWord (M) p)
    let cable:live:=⟨wire.val,alive⟩
    ∃(s:Fin (((sh.sites saved.1).recipe hp).arity saved.2)) (oldWire:Incident W.graph saved.1)
        (oldFits:(piece+1)*p≤W.graph.width oldWire.val) (oldPositive:0<cap.placement.grainCount oldWire.val),
      s.val=j.val ∧ ((sh.sites saved.1).recipe hp).operand saved.2 s=.inl ⟨.inl oldWire,piece,oldFits⟩ ∧
      CablePort cap.placement he ⟨oldWire.val,oldPositive⟩ (if W.graph.src oldWire.val=saved.1 then 0 else 1)
        (parent_ cable) (DescentCableDonorNames.role cable.val)
theorem original_old_cable : OriginalOldCableStatement ticket arch hp one pin sh unit := by
  intro x j saved origin wire piece fits read alive cable
  have trueOrigin:=((names).apply_symm_apply (roots ticket arch x)).trans origin
  obtain ⟨s,oldWire,oldFits,num,previous,mapped⟩:=DescentOrdinaryRawOperandOrigin.real_old_wire arch.bit G (r).pick uni room prof
    hp sh.sites sh.edges pin whole (source x).1 (source x).2 (sourceIndex ticket arch hp one pin sh unit x j)
    saved trueOrigin wire piece fits read
  have positive := positive_grains_of_word hp oldFits (cap.placement.grainCount_fit S cap.valid oldWire.val)
  exact ⟨s,oldWire,oldFits,positive,num.trans (sourceIndex_val ticket arch hp one pin sh unit x j),previous,
    exact_old_port cap.placement he c saved.1 oldWire positive cable mapped⟩

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
