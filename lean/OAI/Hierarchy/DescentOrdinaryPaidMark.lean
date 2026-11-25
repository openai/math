import OAI.Hierarchy.DescentOrdinaryMeasuredParents
import OAI.Hierarchy.DescentOrdinaryResidentMark

namespace OAI
/-! # The measured ordinary roster retains the original parent's signed mark -/
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
set_option maxHeartbeats 2400000
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

variable {hosts groups : ℕ} (name : V₀↪Fin hosts) (groupName : J₀≃Fin groups)
local notation "addr" => parentAddress W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed name groupName
local notation "slot₀" => DescentRawCablePanel.shortSlot prior S installed (edge.trans Fin.valEmbedding) name pick
local notation "kept" => survives W G pick z hz fit pack p key flag k g


open DescentParallelBase.ParentFilter DescentHaloWalkRAM
local notation "U" => Stage.Host J V stage
local notation "headAt" => DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "headEnds" => DescentOrdinaryParentBlocks.head_ends W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "srcAt" => fun h (e : Local C₀ h)=>(world).graph.src (headAt e.val e.property.1)
local notation "dstAt" => fun h (e : Local C₀ h)=>(world).graph.dst (headAt e.val e.property.1)
local notation "oldSite" => fun x : (world).graph.Site=>Stage.home A (ls x)
local notation "hostId" => fun h : U=>h.1.2

variable {D Q K L : ℕ} (R : Fin hosts→Fin D→Option (Fin hosts))
    (hostVenue : V↪Fin hosts×Fin Q)
local notation "raster" => fun h : U=>hostVenue ((hostId) h)
local notation "O" => 2^k₀*prior.cap*11
local notation "Source₀" => Source (breadth D) Q K L
variable (nativeRow : (h : Stage.Host J V stage) → Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h → ParentFilter.Source (breadth D) Q K L)
    (endpoints : ∀h e,Witness R ((parentAddress W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed name groupName) h e).1 (nativeRow h e) (((fun h : (Stage.Host J V stage)=>hostVenue (((fun h : (Stage.Host J V stage)=>h.1.2)) h))) (((DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp)).src e.val)) (((fun h : (Stage.Host J V stage)=>hostVenue (((fun h : (Stage.Host J V stage)=>h.1.2)) h))) (((DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp)).dst e.val)))
    (counts : ∀h e,(nativeRow h e).weight.val=((DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp)).count e.val)
    (orientation : ∀h e,(nativeRow h e).upper=DescentParallelBase.side site (((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h e) (((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.dst ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h e))
    (tickets : ∀h (e f : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h),((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h e=((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h f→
      ((DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1)<(DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) f.val f.property.1) ↔ (nativeRow h e).ticket<(nativeRow h f).ticket))


local notation "Z" => measured W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed name groupName R hostVenue nativeRow endpoints counts orientation tickets

open DescentOrdinarySignedMeta DescentHaloWalkRAM
open scoped Fin.CommRing
variable (symm : ∀v u j,R v j=some u→∃l,R u l=some v)
  (lookup : Fin hosts→Option V₀) (found : ∀v,lookup (name v)=some v)

include found in
/-- This is the mark read by the fixed old-halo query at the address of a
live purchased raw row, including when that same row is viewed from its
opposite endpoint. Neither the emitted core bit nor a donor visit is supplied. -/
theorem paid_mark (h : U) (e : Local C₀ h) :
    let address:=((Measured.roster C₀ R symm Z).address h) e
    let step:Fin (breadth D) × Fin O:=finProdFinEquiv.symm address
    let code:Fin (2^k₀*prior.cap) × Fin 11:=finProdFinEquiv.symm step.2
    let lane:=groupName (digits.symm (h.1.1,h.2))
    MarkGather.flag (decide (code.2.val≠0))
      ((Gather.select (Gather.reaching R) ((Z).venue h).1 step.1).bind (fun donor=>
        donorPanel W G prior (edge.trans Fin.valEmbedding) S installed rank lookup groupName.symm step.2 donor lane))=
      ((decide (e.val∈(coarse).core)).toNat:DescentSIMDLookup.Cell 1) := by
  intro address step code lane
  let donor:=donors h e
  let visit:=Measured.visit C₀ R symm Z h e
  have step_eq : step=(visit,(slot₀ donor).2) := by
    change finProdFinEquiv.symm (finProdFinEquiv _) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have reached : Gather.select (Gather.reaching R) ((Z).venue h).1 visit=some (slot₀ donor).1 :=
    Resident.visit_read C₀ h (fun h=>((Z).venue h).1) (Z).loc ((Z).raw h) (Gather.reaching R)
      (Measured.near C₀ R symm Z h) e
  have born : groupName.symm lane=DescentRawCablePanel.birthGroup prior pick donor := by
    rw [show groupName.symm lane=digits.symm (h.1.1,h.2) from groupName.symm_apply_apply _]
    exact (parent_group W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp
      prior installed rank digits ports actual placed h e).symm
  let readAt (t : Fin (breadth D) × Fin O) :=
    let digits : Fin (2^k₀*prior.cap) × Fin 11 := finProdFinEquiv.symm t.2
    MarkGather.flag (decide (digits.2.val≠0))
      ((Gather.select (Gather.reaching R) ((Z).venue h).1 t.1).bind (fun host =>
        donorPanel W G prior (edge.trans Fin.valEmbedding) S installed rank lookup groupName.symm t.2 host lane))
  change readAt step=_
  refine (congrArg readAt step_eq).trans ?_
  exact shortSlot_mark W G pick z hz fit pack p key flag k g prior (edge.trans Fin.valEmbedding) S installed rank
    name lookup found groupName.symm e.val donor.property (Gather.reaching R) ((Z).venue h).1 visit lane reached born

end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
