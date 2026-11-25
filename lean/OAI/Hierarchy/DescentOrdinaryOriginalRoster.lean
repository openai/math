import OAI.Hierarchy.DescentOrdinaryParentShelf

namespace OAI
/-! The signed parent table and its incidence indices come from one immutable original row file. -/
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

include present in
omit [DecidableEq I] in
private theorem parent_exists (h:U) (t:Local C₀ h) : ∃s,values (headRow h t)=some s :=by
  have mass:=Cweight t.val
  change (C₀).count t.val*q=bitsAt (headRow h t).val at mass
  apply present
  · exact t.val.property
  · rw [←mass,Nat.mul_div_cancel _ qp]
    exact t.property.1

def parentRecord (h:U) (t:Local C₀ h) : Source₀ :=
  (parent_exists W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed
    values present h t).choose

local notation "chosen" => parentRecord W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed values present

omit [DecidableEq I] in
theorem parent_record_read (h:U) (t:Local C₀ h) : values (headRow h t)=some (chosen h t) :=
  (parent_exists W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed
    values present h t).choose_spec

local notation "reading" => parent_record_read W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed values present

include extent in
omit [DecidableEq I] in
theorem parent_record_mass (h:U) (t:Local C₀ h) : (chosen h t).weight.val=(C₀).count t.val :=by
  have mass:=extent (headRow h t) _ (reading h t)
  rw [ite_eq_left (show kept (headRow h t).val from t.val.property)] at mass
  refine mass.trans ?_
  have pos:=Cweight t.val
  change (C₀).count t.val*q=bitsAt (headRow h t).val at pos
  rw [←pos,Nat.mul_div_cancel _ qp]

include ends in
omit [DecidableEq I] in
theorem parent_record_ends (h:U) (t:Local C₀ h) : Witness R (addr h t).1 (chosen h t)
    ((raster) ((C₀).src t.val)) ((raster) ((C₀).dst t.val)) :=
  ends (headRow h t) _ (reading h t)

local notation "leftRight" => parent_record_ends W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed name groupName R hostVenue values present ends
local notation "amount" => parent_record_mass W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed values present extent
variable (direction:∀h (t:Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h),∀s,values ((donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed) h t)=some s→s.upper=DescentParallelBase.side site (((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h t) (((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.dst ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h t))
variable (compare:∀h (a b:Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h),∀s t,values ((donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed) h a)=some s→values ((donorRows W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed) h b)=some t→
  ((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h a=((fun h (e : Local (DescentOrdinaryParentBlocks.blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp) h)=>((DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected)).graph.src ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) e.val e.property.1))) h b→((DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) a.val a.property.1)<(DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) ((DescentOrdinaryParentBlocks.head W G edge pair pick z hz fit pack p key flag k g q old picked affected site A) b.val b.property.1) ↔ s.ticket<t.ticket))
local notation "flagRead" => fun h t=>direction h t _ (reading h t)
local notation "orderRead" => fun h a b=>compare h a b _ _ (reading h a) (reading h b)

abbrev priorMeasurement := measured W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp
  prior installed rank digits ports actual placed name groupName R hostVenue chosen leftRight amount flagRead orderRead

abbrev priorShelf := shelf W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp
  prior installed rank digits ports actual placed name groupName R hostVenue chosen leftRight amount flagRead orderRead
  (fun _ e=>values e) (fun _ e r hit=>extent e r hit) (fun _ e r hit=>ends e r hit) reading

end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
