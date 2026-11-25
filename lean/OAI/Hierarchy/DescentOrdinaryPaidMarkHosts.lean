import OAI.Hierarchy.DescentOrdinaryPaidMarkKnown
import OAI.Hierarchy.DescentDatedSignedHome

namespace OAI
/-! The core bit at an original measured parent ordinal on the normalized host and group chart. -/
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

open DescentDatedAddressBook.SignedExtent
variable {H₁ G₁ : ℕ} (group : J≃Fin G₁) (host : V↪Fin H₁) (pitch : ℕ)

local notation "home" => wholeHost group.toEmbedding host
local notation "groupAt" => fun a : Fin (G₁*2^stage) => groupName (digits.symm (group.symm (finProdFinEquiv.symm a).1,(finProdFinEquiv.symm a).2))
local notation "newRole" => (fun o : Fin O=>decide ((finProdFinEquiv.symm o : Fin (2^k₀*prior.cap) × Fin 11).2.val≠0))
local notation "original" => (fun o v j=>donorPanel W G prior (edge.trans Fin.valEmbedding) S installed rank lookup groupName.symm o v (groupAt j))

include found in
theorem paid_mark_at_hosts
    (physical : ∀u : U,(host u.1.2).val=((Z).venue u).1.val*pitch+((Z).venue u).2.val)
    (lowFits : ∀u : U,((Z).venue u).2.val<pitch)
    (x : Fin (2^stage)) (j : Fin (breadth D*O)) (v : Fin H₁) (g₁ : Fin G₁)
    (u : U) (issued : home x v g₁=some u) (e : Local C₀ u) (hit : (Measured.roster C₀ R symm Z).address u e=j) :
    (DescentOrdinaryMarkProject.bits (Gather.select (Gather.reaching R)) original newRole pitch x j v g₁).val=1 ↔ e.val∈(coarse).core :=by
  have origin (x v g u) (live : home x v g=some u) :
      DescentOrdinaryCompactPeer.ROM.rack hosts pitch v=some ((Z).venue u).1 :=by
    have coordinates:=(wholeHost_iff group.toEmbedding host _ _ _ _).mp live
    have pos : 0<pitch := Nat.zero_lt_of_lt (lowFits u)
    have dvd : v.val/pitch=((Z).venue u).1.val :=by
      rw [←coordinates.2.1,physical u,Nat.mul_comm _ pitch,Nat.mul_add_div pos,Nat.div_eq_of_lt (lowFits u),Nat.add_zero]
    unfold DescentOrdinaryCompactPeer.ROM.rack
    rw [dite_eq_left ⟨pos,dvd ▸ ((Z).venue u).1.isLt⟩]
    exact congrArg some (Fin.ext dvd)
  have lane (x v g u) (live : home x v g=some u) :
      groupAt (finProdFinEquiv (g,x))=groupName (digits.symm (u.1.1,u.2)) :=by
    obtain ⟨groupAtSite,_,blockAtSite⟩:=(wholeHost_iff group.toEmbedding host _ _ _ _).mp live
    change group u.1.1=g at groupAtSite
    simp only [Equiv.symm_apply_apply,←groupAtSite,←blockAtSite]
  exact paid_mark_known W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready
    grain qp prior installed rank digits ports actual placed name groupName R hostVenue nativeRow endpoints counts orientation
    tickets symm lookup found (home) pitch (groupAt) origin lane x j v g₁ u issued e hit

end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
