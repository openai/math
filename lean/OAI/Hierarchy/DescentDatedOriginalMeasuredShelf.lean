import OAI.Hierarchy.DescentDatedOriginalRetainedRecord
import OAI.Hierarchy.DescentOrdinarySignedEmission
import OAI.Hierarchy.DescentIncidentMeasuredOrder

namespace OAI
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
open DescentParallelBase.ParentFilter
omit [DecidableEq I] in
private theorem donor_head_side (h : Stage.Host J V stage) (e : Local C₀ h) :
    let take := DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag
      k g q old picked affected site A e.val e.property.1
    DescentParallelBase.side site ((world).graph.src take) ((world).graph.dst take) =
      DescentParallelBase.side site (lastSite (firstSite (src₀ (donors h e).val)))
        (lastSite (firstSite (dst₀ (donors h e).val))) := by
  intro take
  have both := DescentOrdinaryParentBlocks.head_ends W G edge pair pick z hz fit pack p key flag
    k g q old picked affected site A e.val e.property.1
  exact congrArg₂ (DescentParallelBase.side site) both.1 both.2

omit [DecidableEq I] in
private theorem donor_signed_direction {R : Type} (values : DescentRawCablePanel.Live prior pick → Option R)
    (upper : R → Bool) (rowSide : ∀e r, values e = some r →
      upper r = DescentParallelBase.side site (lastSite (firstSite (src₀ e.val)))
        (lastSite (firstSite (dst₀ e.val)))) (h : Stage.Host J V stage)
    (e : Local C₀ h) (r : R) (read : values (donors h e) = some r) :
    let take := DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag
      k g q old picked affected site A e.val e.property.1
    upper r = DescentParallelBase.side site ((world).graph.src take) ((world).graph.dst take) := by
  intro take
  exact (rowSide (donors h e) r read).trans
    (donor_head_side W G edge pair pick z hz fit pack p key flag k g q old picked affected
      site A S ready grain qp prior installed h e).symm


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

section
variable (named : prior.SiteNamed (groupRank (groupName.toEmbedding.trans Fin.valEmbedding) (name.trans Fin.valEmbedding)))

include named actual placed in
omit [DecidableEq I] in
private theorem donor_ticket_order {R : Type} {K : ℕ}
    (values : DescentRawCablePanel.Live prior pick → Option R) (recordTicket : R → Fin K)
    (rowOrder : ∀ (a b : DescentRawCablePanel.Live prior pick) (s t : R),
      values a = some s → values b = some t →
      lastSite (firstSite (src₀ a.val)) = lastSite (firstSite (src₀ b.val)) →
      (recordTicket s < recordTicket t ↔
        (slot₀ a).1 < (slot₀ b).1 ∨ (slot₀ a).1 = (slot₀ b).1 ∧ (slot₀ a).2 < (slot₀ b).2))
    (h : Stage.Host J V stage) (e f : Local C₀ h) (s t : R)
    (ea : values (donors h e) = some s) (fb : values (donors h f) = some t)
    (common : (world).graph.src (headAt e.val e.property.1) = (world).graph.src (headAt f.val f.property.1)) :
    sparse (headAt e.val e.property.1) < sparse (headAt f.val f.property.1) ↔ recordTicket s < recordTicket t := by
  let a := donors h e
  let b := donors h f
  have same : lastSite (firstSite (src₀ a.val)) = lastSite (firstSite (src₀ b.val)) :=
    (headEnds e.val e.property.1).1.symm.trans (common.trans (headEnds f.val f.property.1).1)
  have rawOrder := rowOrder a b s t ea fb same
  have physical := parentAddress_head_order W G edge pair pick z hz fit pack p key flag k g q old picked affected
    site A S ready grain qp prior installed rank digits ports actual placed name groupName named h e f common
  have left := parentAddress_val W G edge pair pick z hz fit pack p key flag k g q old picked affected
    site A S ready grain qp prior installed rank digits ports actual placed name groupName h e
  have right := parentAddress_val W G edge pair pick z hz fit pack p key flag k g q old picked affected
    site A S ready grain qp prior installed rank digits ports actual placed name groupName h f
  let earlier (u v : Fin hosts × Fin (2^k₀*prior.cap*11)) := u.1<v.1 ∨ u.1=v.1 ∧ u.2<v.2
  let transport := congrArg₂ earlier left right
  exact physical.trans ((Iff.of_eq transport).trans rawOrder.symm)

end

variable {D Q K L : ℕ} (R : Fin hosts→Fin D→Option (Fin hosts))
    (hostVenue : V↪Fin hosts×Fin Q)
local notation "raster" => fun h : U=>hostVenue ((hostId) h)
local notation "O" => 2^k₀*prior.cap*11
local notation "Source₀" => Source (breadth D) Q K L
local notation "live" => DescentRawCablePanel.Live prior pick
local notation "family" => DescentRawCablePanel.birthGroup prior pick
local notation "priorSlot" => DescentRawCablePanel.shortSlot prior S installed (edge.trans Fin.valEmbedding) name pick
local notation "Cweight" => DescentOrdinaryParentBlocks.weight_width W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain
variable (values : DescentRawCablePanel.Live prior pick → Option (ParentFilter.Source (breadth D) Q K L))
variable (present:∀e:(DescentRawCablePanel.Live prior pick),(survives W G pick z hz fit pack p key flag k g) e.val→0<(GadgetNetwork.width (W.graph) pick (branchWidth G z p)) e.val/q→∃s,values e=some s)
variable (extent:∀e:(DescentRawCablePanel.Live prior pick),∀s,values e=some s→s.weight.val=(if (survives W G pick z hz fit pack p key flag k g) e.val then (GadgetNetwork.width (W.graph) pick (branchWidth G z p)) e.val/q else 0))
variable (ends:∀e:(DescentRawCablePanel.Live prior pick),∀s,values e=some s→Witness R ((DescentRawCablePanel.shortSlot prior S installed (edge.trans Fin.valEmbedding) name pick) e).1 s
    (((fun h : (Stage.Host J V stage)=>hostVenue (((fun h : (Stage.Host J V stage)=>h.1.2)) h))) (((fun s=>Stage.home A ((rename site) ((MarkedWorld.address (W.selected G pick z hz fit pack p) key flag k g) ((newSite (W.graph) pick (bestLayout (branchWidth G z p)) pack) s))))) ((GadgetNetwork.source (I:=I) (W.graph)) e.val))) (((fun h : (Stage.Host J V stage)=>hostVenue (((fun h : (Stage.Host J V stage)=>h.1.2)) h))) (((fun s=>Stage.home A ((rename site) ((MarkedWorld.address (W.selected G pick z hz fit pack p) key flag k g) ((newSite (W.graph) pick (bestLayout (branchWidth G z p)) pack) s))))) ((GadgetNetwork.target (W.graph) pick) e.val))))
local notation "headRow" => donors

variable (direction:∀h (t:Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h),∀s,values ((donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed) h t)=some s→s.upper=DescentParallelBase.side site (((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h t) (((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.dst ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h t))
variable (compare:∀h (a b:Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h),∀s t,values ((donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed) h a)=some s→values ((donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed) h b)=some t→
  ((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h a=((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h b→((DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) a.val a.property.1)<(DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) b.val b.property.1) ↔ s.ticket<t.ticket))
variable (reciprocal : ∀v u j,R v j=some u→∃l,R u l=some v)
local notation "Z₀" => priorMeasurement W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp
  prior installed rank digits ports actual placed name groupName R hostVenue values present extent ends direction compare
local notation:max "rawSrc" h:arg e:arg => (src₀) (donors h e).val
local notation:max "rawRank" x:arg => site (lastSite (firstSite x))
local notation:max "rawVenue" x:arg => (raster) ((cell) x)
omit [DecidableEq I] in
private theorem prior_incidence_from_rows
    (compareRows : ∀ (h : U) (e f : Local C₀ h),
      let x := rawSrc h e
                  let y := rawSrc h f
                  (rawVenue x).1 < (rawVenue y).1 ∨ (rawVenue x).1 = (rawVenue y).1 ∧ (rawVenue x).2 < (rawVenue y).2 ↔
                    rawRank x < rawRank y)
    (h : U) (e f : Local C₀ h) :
    Incidence.srcKey C₀ R reciprocal Z₀ h e < Incidence.srcKey C₀ R reciprocal Z₀ h f ↔
      (Z₀).site ((Z₀).src ((Z₀).head h e)) < (Z₀).site ((Z₀).src ((Z₀).head h f)) := by
  refine (Incidence.native_order C₀ R reciprocal Z₀ h e f).trans ?_
  change _ ↔ site ((world).graph.src (headAt e.val e.property.1)) < site ((world).graph.src (headAt f.val f.property.1))
  rw [(headEnds e.val e.property.1).1,(headEnds f.val f.property.1).1]
  exact compareRows h e f
end
end Hierarchy.DescentOrdinaryParentSupport

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentParallelBase DescentSharedCableNames
open scoped Classical
noncomputable section

private theorem blocks_source_band {F P J V E : Type} [Field F]
    [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {d k : ℕ}
    {bits : P → ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
    (C : Blocks (Stage.source A native) E) (h : Stage.Host J V k) (e : Local C h) :
    (C.src e.val).1.1 = h.1.1 ∧ (C.src e.val).2 = h.2 := by
  rcases e.property.2 with atSrc | atDst
  · exact ⟨congrArg (fun u : Stage.Host J V k => u.1.1) atSrc,
      congrArg (fun u : Stage.Host J V k => u.2) atSrc⟩
  · let j : Fin (C.count e.val) := ⟨0, e.property.1⟩
    let grain := C.order ⟨e.val, j⟩
    let edge := ((Stage.stream A native).symm grain).1
    have src : Stage.home A (W.graph.src edge) = C.src e.val := C.atSource e.val j
    have dst : Stage.home A (W.graph.dst edge) = h := (C.atTarget e.val j).trans atDst
    obtain ⟨_, _, point⟩ := Finset.mem_map.mp (A.peers edge).1
    have pointGroup := congrArg Prod.fst point
    have groupEq : (A.pos (W.graph.src edge)).1 = (A.pos (W.graph.dst edge)).1 := pointGroup
    have blockEq := A.same edge
    exact ⟨(congrArg (fun u : Stage.Host J V k => u.1.1) src).symm.trans
        (groupEq.trans (congrArg (fun u : Stage.Host J V k => u.1.1) dst)),
      (congrArg (fun u : Stage.Host J V k => u.2) src).symm.trans
        (blockEq.trans (congrArg (fun u : Stage.Host J V k => u.2) dst))⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip packDonor StarKeys.nativeKey OrdinaryLink.donorKey OrdinaryLink.measuredDonors
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "V" => prior.V
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
variable (b : ℕ) (m : Memory w)
    (sumSize : (shape (2^k) prior.placement.degree (2*prior.placement.cap) profile).outputBits*port.groupsPerWord≤w)
    (stored :
      let rankAt:=groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)
      let shape₀:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) shape₀ prior.placement.cap partsAt)
      ∀j,m (b+j.val)=((DescentPacking.PackedMatch.topologyWords (M:=port.groupsPerWord) shape₀ inputs j).val:Computability.VPVNP.BurstRAM.Word w))
variable (dest : ℕ) (issued : Memory w)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "measured" => Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm profile dest issued roster (A).hub lay bytes

open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator

local notation "sampleSlot" => DescentRawCablePanel.slot A S prior.valid native hosts grp (rr).pick
local notation "oldPorts" => S.groupCount i*(2^k)*(A).cap

variable (birth :
    let stage:=prior.placement.stage
    let actor:=scanHomeAt he stage
    let tint:=scanColorAt he stage
    let flow:=nativeTraffic W.graph W.core actor
    let limit:=prior.placement.cap
    let shape₀:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin shape₀.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (shape₀.digit+1) ip.val (issued (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

local notation "N" => rawGraph he T choice
local notation "owner" => rawOwner he T choice n ((rr).state choice) (originalId _)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation:max "units" h:arg j:arg => liveMass (report (T).k gain slots
  (DepotRAM.seatDonor fmt profile G.b slots (measured h (groupSeat j).1) (groupSeat j).2.1 (groupSeat j).2.2.1)
  (groupSeat j).2.2.2)

open DescentSharedCableNames DescentHaloPackedRebase DescentParallelBase.ParentFilter
local notation "homeAt" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "ctr" e:arg => mergeHub ticket.donorHub (T).k gain (ticket.donorKey (homeAt e))
local notation "P₀" => breadth (A).degree
local notation "Q" => 2^((T).k+1)*slots
local notation "K₀" => (P₀+1)*DepotRAM.Material.roles fmt
local notation "pitch" => (2^((T).k+1)-1)*slots
variable (fieldBits : ℕ)
local notation "form" => rawFormat (G:=G) (prior:=prior) profile pitch fieldBits
local notation "roomAt" => original_parent_room ticket port win hm named fit winner df order profile b m sumSize stored
                            dest issued roster mounted birth pitch fieldBits roster
local notation:max "rev" h:arg => digest (DepotRAM.Material.reverseEntries fmt roster h)

local notation:max "cell" h:arg j:arg => originalRecord ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits h (groupSeat j).1 (groupSeat j).2
local notation:max "current" x:arg => n.destination (rawInput he T choice ((rr).state choice) x)
local notation:max "venue" x:arg => ticket.parentVenue port.enough (next.placement.pos (current x)).2
local notation:max "endRack" e:arg => hosts (ticket.donorKey (homeAt e)).1.2
local notation:max "endLow" e:arg => SiteDecode.localNumber (T).k slots (ctr e)

variable (age:i<S.length) (radix:S.radix=2^k)

variable (B:OrdinaryModel he prior.placement.stage choice (Fin (S.groupCount i)×prior.V))
local notation "world" => (B.named he T choice prior.order).result
local notation "act" => B.rawSite he T choice
variable (coh:n.result=(B.named he prior.placement.stage choice prior.order).result)
variable (places:∀x:(rawGraph he prior.placement.stage choice).Site,
  cast (congrArg (fun u:MarkedWorld F d P bits=>u.graph.Site) coh)
    (n.destination (rawInput he prior.placement.stage choice ((BitDescription.scannedRows he prior.placement.stage).state choice) x))=
    B.rawSite he prior.placement.stage choice x)
local notation "A₁" => modelStage (next:=next) B coh
local notation:max "raster₁" x:arg => ticket.parentVenue port.enough ((A₁).pos (act x)).2
local notation "key" => B.chart.key he T choice
local notation "last" => DescentSixParty.MarkedWorld.address (W.selected G (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice))
  key B.chart.hub (T).k gain
local notation:max "survives" e:arg => last (homeAt ((N).src (e).val))≠last (homeAt ((N).dst (e).val))
local notation:max "valueAt" e:arg => cell (sampleSlot e).1 (sampleSlot e).2
variable (pathWidth:breadth prior.placement.degree<2^fieldBits)
  (ticketWidth:(breadth prior.placement.degree+1)*DepotRAM.Material.roles
    (Stage.shapeOf (short:=short) prior.placement (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))≤2^fieldBits)
local notation "full" => original_record_full (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth pitch fieldBits age radix pathWidth ticketWidth

open DescentParallelBase DescentOrdinaryParentSupport DescentSharedCableNames DescentSixParty.MarkedWorld
local notation "targetRows" => Source P₀ Q K₀ next.placement.cap
local notation "dataAt" => fun e:positiveRows=>valueAt e
local notation "pairNo" => PairRAM.globalNumberBy W.graph W.core home color (T).cap (originalId (ScanColonies he T))
local notation "oldCut" => B.old
local notation "chosenCut" => B.used
local notation "stageCut" => fun _ : (rr).pairs=>dvd_refl (T).z
local notation "ok" => model_bounds (next:=next) B coh
local notation "eqG" => model_grain ticket B coh
local notation "paths" => modelPaths (short:=short) (prior:=prior) (choice:=choice) win profile
local notation "routes" => model_paths (short:=short) (prior:=prior) (choice:=choice) win named fit winner df order profile B
local notation "groups'" => S.groupDigits age radix
local notation "placed" => fun x=> (model_sites ticket port age radix B coh places x).1
local notation "atV" => ticket.parentVenue port.enough
local notation "host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) next.V k
local notation "C₀" => DescentOrdinaryParentBlocks.blocks W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ (T).unitPos
local notation "donors" => DescentOrdinaryParentSupport.donorRows W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid
local notation "heads" => DescentOrdinaryParentBlocks.head W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁
local notation "headEnds" => DescentOrdinaryParentBlocks.head_ends W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁
local notation "addr'" => DescentOrdinaryParentSupport.parentAddress W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid rank groups' paths routes placed hosts grp
local notation "sub" => (B.normalized he T choice).result
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  DescentOrdinarySiblingSerial.worldKey from OAI.Hierarchy.DescentOrdinarySiblingSerial
local notation "physicalBase" => DescentOrdinarySiblingSerial.physicalBase W G (rr).pick
  (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub
  (T).k gain (T).z oldCut chosenCut stageCut
local notation "order₀" => (B.tape he T choice prior.order).sourceKey (sub).graph.src B.site (sub).graph.width
attribute [local irreducible] originalRecord
set_option maxHeartbeats 1200000

local notation "fields" => model_original_fields (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth fieldBits age radix B coh places pathWidth ticketWidth
local notation "exists_" => model_original_present (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored
    dest issued roster mounted birth fieldBits B coh places pathWidth ticketWidth

include age radix places pathWidth ticketWidth in
private theorem original_extent (e:positiveRows) (r:targetRows) (seen:valueAt e=some r) :
    (r).weight.val=(if survives e then (N).width e.val/(T).z else 0):=by
  have reading := fields e (r:=r) seen
  exact reading.2.2.1.trans (ite_eq_left reading.1).symm

include age radix places pathWidth ticketWidth in
private theorem original_raw_direction (e:positiveRows) (s:targetRows) (read:valueAt e = some s) :
    s.upper = DescentParallelBase.side B.site
      (last (homeAt (GadgetNetwork.source (I:=(rr).pairs) W.graph e.val)))
      (last (homeAt (GadgetNetwork.target W.graph (rr).pick e.val))) := by
  have raw := (fields e (r:=s) read).2.2.2.2
  dsimp only [rawGraph, GadgetNetwork.physical] at raw
  exact raw

private abbrev original_dir := DescentOrdinaryParentSupport.donor_signed_direction W G prior.order pairNo (rr).pick
    (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub
    (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid
    dataAt (fun s : targetRows => s.upper)
    (original_raw_direction (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit
      winner df order profile b m sumSize stored dest issued roster mounted birth fieldBits age radix B coh
      places pathWidth ticketWidth)

private theorem short_row (t:positiveRows) :
    shortSlot A S prior.valid native hosts (rr).pick t=((sampleSlot t).1,DescentOrdinaryIssuedTicket.within (sampleSlot t).2):=by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    rw [DescentOrdinaryIssuedTicket.within_read]
    simp only [shortSlot,finProdFinEquiv_apply_val]
    ring

variable (reciprocal:∀v u j,roster v j=some u→∃l,roster u l=some v)
include age radix places pathWidth ticketWidth in
private theorem original_live_record (e:positiveRows) (s:targetRows) (read:valueAt e=some s) :
    owner ((N).src e.val)≠owner ((N).dst e.val) ∧ 0<(N).width e.val/(A).z :=by
  have data := fields e (r:=s) read
  exact ⟨(model_different B coh places _ _).1 data.1,data.2.1⟩


local notation "liveRecord" => original_live_record (prior:=prior) (short:=short) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
    birth fieldBits age radix B coh places pathWidth ticketWidth
local notation "asSlot" => shortSlot A S prior.valid native hosts (rr).pick

include age radix places pathWidth ticketWidth reciprocal in
private theorem original_row_ticket_order (e f:positiveRows) (s t:targetRows)
    (ea:valueAt e=some s) (fb:valueAt f=some t)
    (common:last (homeAt (GadgetNetwork.source (I:=(rr).pairs) W.graph e.val))=
      last (homeAt (GadgetNetwork.source (I:=(rr).pairs) W.graph f.val))) :
    s.ticket<t.ticket ↔ (asSlot e).1<(asSlot f).1 ∨ (asSlot e).1=(asSlot f).1 ∧ (asSlot e).2<(asSlot f).2 :=by
  have keep:∀j∈([e,f]:List _),owner ((N).src j.val)≠owner ((N).dst j.val) ∧ 0<(N).width j.val/(A).z:=by
    intro j mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact liveRecord j s ea
    · exact liveRecord j t fb
  have legal : owner ((N).src e.val)=owner ((N).src f.val):=by
    by_contra apart
    apply (model_different B coh places _ _).2 apart
    exact common
  have trueOrder:=original_record_order ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
    birth pitch fieldBits age radix pathWidth ticketWidth reciprocal e f keep legal ea fb
  let earlier (u v : Fin H × Fin (2^k*(A).cap*11)) : Prop :=
    u.1<v.1 ∨ u.1=v.1 ∧ u.2<v.2
  have transport := congrArg₂ earlier (short_row (prior:=prior) (he:=he) port e) (short_row (prior:=prior) (he:=he) port f)
  exact trueOrder.trans (Iff.of_eq transport.symm)

private abbrev original_less := DescentOrdinaryParentSupport.donor_ticket_order W G prior.order pairNo (rr).pick
    (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub
    (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid
    rank groups' paths routes placed hosts grp named dataAt (fun r : targetRows => r.ticket)
    (original_row_ticket_order (prior:=prior) (short:=short) (w:=w) (a:=a)
      ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
      birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal)

private theorem weight_of_retained {c : Prop} {check : Decidable c} {out width : ℕ}
    (kept : c) (massRead : out=width) : out = @ite ℕ c check width 0 := by
  let := check
  simpa only [ite_eq_left kept] using massRead
local notation "mass" => fun e r hit => by
  have fs := fields e (r:=r) hit
  exact weight_of_retained fs.1 fs.2.2.1
local notation "orientation" => fun h t s rd => original_dir (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
    birth fieldBits age radix B coh places pathWidth ticketWidth h t s rd
local notation "comparison" => fun h e f s t ea fb eqn => original_less (prior:=prior) (short:=short) (w:=w) (a:=a) ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
    birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal h e f s t ea fb eqn
local notation "endRead" => fun e r hit=>(fields e (r:=r) hit).2.2.2.1

/-- The measured signed roster comes entirely from the preceding topology, selected
birth rows, old signed order, host adjacency and a single genuine normalized presentation. -/
abbrev originalMeasurement := DescentOrdinaryParentSupport.priorMeasurement W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid rank groups' paths routes placed hosts grp roster atV dataAt exists_ mass endRead orientation comparison

/-- Every query of the measured old roster uses the same physically emitted old record,
with no independent data at the receiving endpoint. -/
abbrev originalShelf := DescentOrdinaryParentSupport.priorShelf W G prior.order pairNo (rr).pick (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid rank groups' paths routes placed hosts grp roster atV dataAt exists_ mass endRead orientation comparison
local notation "measurement" => originalMeasurement (prior:=prior) (short:=short) (w:=w) (a:=a)
  ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
  birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal

include places in
/-- Whichever end the receiver observes, the first surviving physical edge puts
the parent's source in this receiver's group and block. -/
private theorem original_source_band (h:host)(e:Local C₀ h):
    let x:=(N).src (donors h e).val
    (next.placement.pos (current x)).1=h.1.1 ∧ next.placement.block (current x)=h.2:=by
  intro x
  have sharp : ((C₀).src e.val).1.1=h.1.1 ∧ ((C₀).src e.val).2=h.2 := blocks_source_band A₁ (originalId (world).graph.Edge) C₀ h e
  have here : ((A₁).pos (act x)).1=h.1.1 ∧ (A₁).block (act x)=h.2 := sharp
  have moved := model_placement (next:=next) B coh places x
  exact ⟨(congrArg Prod.fst moved.1).symm.trans here.1, moved.2.symm.trans here.2⟩

private theorem physical_band_order (x y : n.result.graph.Site)
    (gEq:(next.placement.pos x).1=(next.placement.pos y).1)
    (bEq:next.placement.block x=next.placement.block y):
    let vx:=ticket.parentVenue port.enough (next.placement.pos x).2
    let vy:=ticket.parentVenue port.enough (next.placement.pos y).2
    vx.1<vy.1 ∨ vx.1=vy.1 ∧ vx.2<vy.2 ↔ originalId n.result.graph.Site x<originalId n.result.graph.Site y :=by
  dsimp only
  let px:=next.placement.pos x
  let py:=next.placement.pos y
  let vx:=ticket.parentVenue port.enough px.2
  let vy:=ticket.parentVenue port.enough py.2
  let packed:=next.placement.siteSlot next.vertex next.valid.coordinates
  have compareSlots : (packed x).val<(packed y).val ↔ originalId _ x<originalId _ y:=by
    have ix:=next.siteName (Nat.succ_pos _) x
    have iy:=next.siteName (Nat.succ_pos _) y
    exact (DescentPhysicalOrder.physical_lt_iff (DescentSiteTape.rank packed) x y).symm.trans
      (congrArg₂ (fun a b : ℕ=>a<b) ix iy).symm.to_iff
  refine Iff.trans ?_ compareSlots
  have xSlot := GroupStage.siteSlot_val next.placement next.vertex next.valid.coordinates x
  have ySlot := GroupStage.siteSlot_val next.placement next.vertex next.valid.coordinates y
  refine Iff.trans ?_ (congrArg₂ (fun a b : ℕ=>a<b) xSlot ySlot).symm.to_iff
  change _ ↔ (px.1.val*Fintype.card next.V+(next.vertex px.2).val)*2^k+(next.placement.block x).val<
    (py.1.val*Fintype.card next.V+(next.vertex py.2).val)*2^k+(next.placement.block y).val
  have groupVal : px.1.val=py.1.val:=congrArg Fin.val gEq
  have blockVal := congrArg Fin.val bEq
  simp only [groupVal,blockVal,Nat.add_lt_add_iff_right,Nat.mul_lt_mul_right (Nat.two_pow_pos _),Nat.add_lt_add_iff_left]
  have ord := congrArg₂ (fun a b : ℕ=>a<b) (ticket.parentVenue_ordinal port.enough px.2)
    (ticket.parentVenue_ordinal port.enough py.2)
  refine Iff.trans ?_ ord.symm.to_iff
  refine Iff.trans ?_ (DescentOrdinaryDonorHalo.lex (a:=vx.1.val) (b:=vy.1.val)
    (ticket.parentVenue_low port.enough px.2) (ticket.parentVenue_low port.enough py.2)).symm
  change (vx.1<vy.1 ∨ vx.1=vy.1 ∧ vx.2<vy.2) ↔ (vx.1.val<vy.1.val ∨ vx.1.val=vy.1.val ∧ vx.2.val<vy.2.val)
  simp only [Fin.lt_def,Fin.ext_iff]


include places in
private theorem source_order_at_band (x y:(N).Site)
    (gEq:(next.placement.pos (current x)).1=(next.placement.pos (current y)).1)
    (bEq:next.placement.block (current x)=next.placement.block (current y)):
    (raster₁ x).1<(raster₁ y).1 ∨ (raster₁ x).1=(raster₁ y).1 ∧ (raster₁ x).2<(raster₁ y).2 ↔
      B.site (last (homeAt x))<B.site (last (homeAt y)):=by
  have left:=model_placement (next:=next) B coh places x
  have right:=model_placement (next:=next) B coh places y
  let px:=next.placement.pos (current x)
  let py:=next.placement.pos (current y)
  let vx:=ticket.parentVenue port.enough px.2
  let vy:=ticket.parentVenue port.enough py.2
  have hx : (raster₁ x)=vx:=congrArg (fun pos=>ticket.parentVenue port.enough pos.2) left.1
  have hy : (raster₁ y)=vy:=congrArg (fun pos=>ticket.parentVenue port.enough pos.2) right.1
  let lexAt {a b : ℕ} (l r : Fin a × Fin b) : Prop :=
    l.1<r.1 ∨ l.1=r.1 ∧ l.2<r.2
  have rawOrder:=B.old_rank he T choice prior.order ((rr).state choice) coh places x y
  have nativeOrder:=physical_band_order ticket port (current x) (current y) gEq bEq
  exact (congrArg₂ lexAt hx hy).to_iff.trans (nativeOrder.trans rawOrder)

include places in
private theorem current_donor_order (h : host) (e f : Local C₀ h) :
    let x := (N).src (donors h e).val
    let y := (N).src (donors h f).val
    (raster₁ x).1 < (raster₁ y).1 ∨
      (raster₁ x).1 = (raster₁ y).1 ∧ (raster₁ x).2 < (raster₁ y).2 ↔
      B.site (last (homeAt x)) < B.site (last (homeAt y)) := by
  intro x y
  have a:=original_source_band ticket B coh places h e
  have b':=original_source_band ticket B coh places h f
  exact source_order_at_band ticket port B coh places x y (a.1.trans b'.1.symm) (a.2.trans b'.2.symm)
private abbrev current_incidence_order := DescentOrdinaryParentSupport.prior_incidence_from_rows W G prior.order pairNo (rr).pick
    (fun _=>(T).z) (fun _=>(T).unitPos) (rr).fit (rr).pack ((rr).profile choice) key B.chart.hub (T).k gain (T).z
    oldCut chosenCut stageCut B.site A₁ S ok eqG (T).unitPos A prior.valid rank groups' paths routes placed hosts grp roster atV
    dataAt exists_ mass endRead orientation comparison reciprocal
    (current_donor_order (next:=next) ticket port B coh places)

/-- Source order at a receiving host comes from both directed coordinates in the
actual previous parent records, including comparisons between two incoming cables. -/
theorem original_incidence_orders (h:host)(e f:Local C₀ h):
    let observed := measurement
    Incidence.srcKey C₀ roster reciprocal observed h e < Incidence.srcKey C₀ roster reciprocal observed h f ↔
      observed.site (observed.src (observed.head h e)) < observed.site (observed.src (observed.head h f)) := current_incidence_order (prior:=prior) (short:=short) (w:=w) (a:=a)
    ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
    birth fieldBits age radix B coh places pathWidth ticketWidth reciprocal h e f


end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

-- Premise selection traverses the expanded chronological signatures during export.
-- The filter here applies only while exporting this module.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun current =>
    ["original_incidence_orders"] ++ current

end OAI
