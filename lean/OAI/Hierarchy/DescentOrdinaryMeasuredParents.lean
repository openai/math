import OAI.Hierarchy.DescentOrdinaryParentAddress
import OAI.Hierarchy.DescentOrdinaryPeerBand
import OAI.Hierarchy.DescentParentFilterRoster

namespace OAI
/-! # The measured finite parent roster for an ordinary successor -/
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

include ready in
omit [DecidableEq I] [Fintype J₀] [Fintype V₀] in
theorem same_heads (h : U) (e f : Local C₀ h) (peer : other C₀ h e=other C₀ h f) :
    ((srcAt) h e=(srcAt) h f ∧ (dstAt) h e=(dstAt) h f) ∨
      ((srcAt) h e=(dstAt) h f ∧ (dstAt) h e=(srcAt) h f) := by
  have equal : Function.Injective (oldSite) := ready.coordinates.comp (ls).injective
  have es : (oldSite) ((srcAt) h e)=(C₀).src e.val :=congrArg (oldSite) (headEnds e.val e.property.1).1
  have et : (oldSite) ((dstAt) h e)=(C₀).dst e.val :=congrArg (oldSite) (headEnds e.val e.property.1).2
  have fs : (oldSite) ((srcAt) h f)=(C₀).src f.val :=congrArg (oldSite) (headEnds f.val f.property.1).1
  have ft : (oldSite) ((dstAt) h f)=(C₀).dst f.val :=congrArg (oldSite) (headEnds f.val f.property.1).2
  rcases (other_parallel C₀ h e f).2 peer.symm with ⟨src,dst⟩|⟨src,dst⟩
  · exact Or.inl ⟨equal (es.trans (src.symm.trans fs.symm)),equal (et.trans (dst.symm.trans ft.symm))⟩
  · exact Or.inr ⟨equal (es.trans (dst.symm.trans ft.symm)),equal (et.trans (src.symm.trans fs.symm))⟩

variable {D Q K L : ℕ} (R : Fin hosts→Fin D→Option (Fin hosts))
    (hostVenue : V↪Fin hosts×Fin Q)
local notation "raster" => fun h : U=>hostVenue ((hostId) h)
local notation "O" => 2^k₀*prior.cap*11
local notation "Source₀" => Source (breadth D) Q K L
/-- Only the four physical field reads at originally addressed rooted rows
enter the roster. All underlying raw and typed node identities, their
admissibility, and absolute chronology come from the ordinary successor. -/
def measured
    (nativeRow : (h : U)→Local C₀ h→Source₀)
    (endpoints : ∀h e,Witness R (addr h e).1 (nativeRow h e) ((raster) ((C₀).src e.val)) ((raster) ((C₀).dst e.val)))
    (counts : ∀h e,(nativeRow h e).weight.val=(C₀).count e.val)
    (orientation : ∀h e,(nativeRow h e).upper=DescentParallelBase.side site ((srcAt) h e) ((dstAt) h e))
    (tickets : ∀h (e f : Local C₀ h),(srcAt) h e=(srcAt) h f→
      (sparse (headAt e.val e.property.1)<sparse (headAt f.val f.property.1) ↔ (nativeRow h e).ticket<(nativeRow h f).ticket)) :
    Measured C₀ R (Fin hosts×Fin O) (world).graph.Edge (world).graph.Site Q O K L where
  venue:=raster
  «raw»:=addr
  loc:=Function.Embedding.refl _
  read:=nativeRow
  reached:=endpoints
  otherInj:=fun h e f eqn=>other_venue A ord C₀ hostVenue h e f eqn
  survives:=counts
  «tape»:=tape
  site:=site
  src:=(world).graph.src
  dst:=(world).graph.dst
  width:=(world).graph.width
  head:=fun _ e=>headAt e.val e.property.1
  active:=fun _ e=>DescentOrdinaryParentBlocks.head_width W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready e.val e.property.1
  orientation:=orientation
  samePair:=same_heads W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready qp
  shortTicket:=tickets
  chronology:=fun _ e f=>DescentOrdinaryParentBlocks.first_before W G edge pair pick z hz fit pack p key flag k g q old picked affected site A e.val f.val e.property.1 f.property.1

end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
