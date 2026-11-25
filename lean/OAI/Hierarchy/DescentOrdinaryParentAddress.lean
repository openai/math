import OAI.Hierarchy.DescentOrdinaryParentGroups

namespace OAI
/-! # A signed ordinary parent computes its own group, donor row and role -/
namespace Hierarchy.DescentOrdinaryParentSupport
open DescentPacking.PackedMatch.Local
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentOrdinarySiblingSerial DescentParallelBase
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  from OAI.Hierarchy.DescentOrdinarySiblingSerial
open GadgetNetwork
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P I C J₀ V₀ : Type} [Field F] [Fintype I] [DecidableEq I] [Fintype J₀] [DecidableEq J₀] [Fintype V₀] [DecidableEq V₀] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
local notation "N" => W.graph
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key (J₀×V₀)) (flag : (J₀×V₀)→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "rep" => repetitions W G pick z hz fit pack p key flag k g q
local notation "world" => DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected
local notation "tape" => ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
local notation "sparse" => DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "next" => PhysicalRename.rankedWorld world site sparse
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage : ℕ} {price ε : ℝ}
variable (A : GroupStage
    (PhysicalRename.rankedWorld
      (DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site))
    G price ε J V stage)

local notation "ls" => rename site
local notation "ord" => originalId (next).graph.Edge
local notation "stream'" => Stage.stream A ord
local notation "B" => Stage.source A ord


local notation "raw" => Raw W.graph.Edge I
local notation "sw" => branchWidth G z p
local notation "firstSite" => newSite N pick (bestLayout sw) pack
local notation "lastSite" => MarkedWorld.address sel key flag k g
local notation "bitsAt" => GadgetNetwork.width N pick sw
local notation "src₀" => GadgetNetwork.source (I:=I) N
local notation "dst₀" => GadgetNetwork.target N pick

variable {i a₀ : ℕ} {k₀ : ℕ} {price₀ ε₀ : ℝ} (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (grain : A.z*G.b=q) (qp : 0<q)
  (prior : GroupStage W G price₀ ε₀ J₀ V₀ k₀) (installed : prior.StateBounds S a₀)
local notation "rows" => localRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp
local notation "donors" => donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed
local notation "C₀" => DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp
local notation "cell" => fun s=>Stage.home A (ls (lastSite (firstSite s)))
local notation "oldHost" => fun e : DescentRawCablePanel.Live prior pick=>prior.pos (W.graph.src (anchor pick e.val))
local notation "rotor" => DescentPacking.PackedMatch.Local.Stage.rotor
variable (rank : (J₀×V₀)↪ℕ) (digits : J₀≃J×Block stage)
variable (ports : DescentRawCablePanel.Live prior pick→Option (Walk×Walk))
    (actual : ∀e : DescentRawCablePanel.Live prior pick,
      let first := newSite W.graph pick (bestLayout (branchWidth G z p)) pack
      let left := first (GadgetNetwork.source (I:=I) W.graph e.val)
      let right := first (GadgetNetwork.target W.graph pick e.val)
      (ports e=none → left=right) ∧ ∀walks, ports e=some walks →
        ParentIncidence.Actual (DescentPacking.PackedMatch.Local.Stage.rotor prior rank)
          (prior.pos (W.graph.src (anchor pick e.val))) walks (key left) (key right))
    (placed : ∀s : GadgetNetwork.Site (I:=I) W.graph,
      let first := newSite W.graph pick (bestLayout (branchWidth G z p)) pack s
      let endpoint := MarkedWorld.address (W.selected G pick z hz fit pack p) key flag k g first
      let cellPos := DescentSharedCableNames.Stage.home A (rename site endpoint)
      (cellPos.1.1,cellPos.2) = digits (splitKey endpoint.val).1)

include actual placed in
omit [DecidableEq I] in
theorem parent_group (h : Stage.Host J V stage) (t : Local C₀ h) :
    DescentRawCablePanel.birthGroup prior pick (donors h t)=digits.symm (h.1.1,h.2) := by
  let e:=donors h t
  let a:=firstSite (src₀ e.val)
  let b:=firstSite (dst₀ e.val)
  have measured:=actual e
  apply DescentPacking.PackedMatch.Local.Stage.group_from_parent (width:=k) (g:=g) prior rank digits flag ((oldHost) e)
    (key a) (key b) (ports e) (fun nil=>congrArg key (measured.1 nil)) measured.2
  · exact fun joined=>(rows h t).property.1 (Subtype.ext joined)
  · have side:((cell) (src₀ e.val))=h ∨ ((cell) (dst₀ e.val))=h:=(rows h t).property.2.2
    rcases side with atSrc|atDst
    · exact Or.inl ((congrArg (fun x : Stage.Host J V stage=>(x.1.1,x.2)) atSrc).symm.trans (placed _))
    · exact Or.inr ((congrArg (fun x : Stage.Host J V stage=>(x.1.1,x.2)) atDst).symm.trans (placed _))

variable {hosts groups : ℕ} (name : V₀↪Fin hosts) (groupName : J₀≃Fin groups)
include actual placed in
def parentAddress (h : Stage.Host J V stage) : Local C₀ h↪Fin hosts×Fin (2^k₀*prior.cap*11) :=
  DescentRawCablePanel.ParentGroupSlot.anchored prior S installed (edge.trans Fin.valEmbedding) name groupName pick C₀ h
    (digits.symm (h.1.1,h.2)) (donors h)
    (parent_group W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp
      prior installed rank digits ports actual placed h)

local notation "addr" => parentAddress W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed name groupName
local notation "slot₀" => DescentRawCablePanel.shortSlot prior S installed (edge.trans Fin.valEmbedding) name pick
local notation "kept" => survives W G pick z hz fit pack p key flag k g

include actual placed in
omit [DecidableEq I] in
theorem parentAddress_val (h : Stage.Host J V stage) (t : Local C₀ h) :
    addr h t=slot₀ (donors h t) :=rfl

include actual placed in
omit [DecidableEq I] in
/-- The same fixed physical old address may be inspected on either endpoint.
For the old group selected by this window it is occupied exactly for an
actual positive, non-looping post-trim raw parent incident at this position. -/
theorem address_iff (h : Stage.Host J V stage) (e : DescentRawCablePanel.Live prior pick)
    (inLane : DescentRawCablePanel.birthGroup prior pick e=digits.symm (h.1.1,h.2)) :
    (∃t : Local C₀ h,addr h t=slot₀ e) ↔ kept e.val ∧ 0<bitsAt e.val ∧
      ((cell) (src₀ e.val)=h ∨ (cell) (dst₀ e.val)=h) := by
  constructor
  · rintro ⟨t,slotEq⟩
    let same:=parent_group W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed h t
    let index:=DescentRawCablePanel.byGroup prior S installed (edge.trans Fin.valEmbedding) name groupName pick (digits.symm (h.1.1,h.2))
    have sameDonor : donors h t=e :=congrArg Subtype.val
      (index.injective (show index ⟨donors h t,same⟩=index ⟨e,inLane⟩ from slotEq))
    have sameRaw : (rows h t).val=e.val:=congrArg Subtype.val sameDonor
    exact sameRaw ▸ (rows h t).property
  · intro marked
    let t:Local C₀ h:=(rows h).symm ⟨e.val,marked⟩
    have recovered : donors h t=e := by
      apply Subtype.ext
      change ((rows h) t).val = e.val
      exact congrArg Subtype.val ((rows h).apply_symm_apply ⟨e.val,marked⟩)
    exact ⟨t,congrArg slot₀ recovered⟩


end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
