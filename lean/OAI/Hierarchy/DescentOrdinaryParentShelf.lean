import OAI.Hierarchy.DescentOrdinaryMeasuredParents

namespace OAI
/-! # Support and rejection of every positive ordinary signed parent register -/
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
local notation "live" => DescentRawCablePanel.Live prior pick
local notation "family" => DescentRawCablePanel.birthGroup prior pick
local notation "xaddr" => Fin hosts×Fin O

/-- The sparse physical lookup first checks that the old donor slot is present in
this SIMD group. This test depends only on the prior roster and the accepted roles. -/
def priorAt (h : U) (x : xaddr) : Option live :=
  if found : ∃e : live,family e=digits.symm (band h) ∧ slot₀ e=x then some found.choose else none

include groupName in
omit [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] in
theorem priorAt_live (h : U) (e : live) (here : family e=digits.symm (band h)) :
    priorAt (W:=W) (G:=G) (stage:=stage) (edge:=edge) (pick:=pick) (S:=S) (prior:=prior) (installed:=installed) (digits:=digits) (name:=name) h (slot₀ e)=some e := by
  unfold priorAt
  let found : ∃a : live,family a=digits.symm (band h) ∧ slot₀ a=slot₀ e :=⟨e,here,rfl⟩
  rw [dite_eq_left found]
  let unique:=DescentRawCablePanel.byGroup prior S installed (edge.trans Fin.valEmbedding) name groupName pick (digits.symm (band h))
  exact congrArg some (congrArg Subtype.val (unique.injective (show unique ⟨found.choose,found.choose_spec.1⟩=unique ⟨e,here⟩ from found.choose_spec.2)))

omit [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] in
/-- Reading a compact physical slot and first recovering its old parent agree in every original group. -/
theorem prior_board {α : Type*} (fetch : U→xaddr→Option α)
    (blank : ∀h x,(¬∃e : live,family e=digits.symm (band h) ∧ slot₀ e=x)→fetch h x=none)
    (h : U) (x : xaddr) :
    (priorAt (W:=W) (G:=G) (stage:=stage) (edge:=edge) (pick:=pick) (S:=S) (prior:=prior)
      (installed:=installed) (digits:=digits) (name:=name) h x).bind (fun e=>fetch h (slot₀ e))=fetch h x :=by
  unfold priorAt
  split
  next has => simp [has.choose_spec.2]
  next missing => simp [blank h x missing]

variable (rawRecord : Stage.Host J V stage → DescentRawCablePanel.Live prior pick → Option (ParentFilter.Source (breadth D) Q K L))
local notation "readOld" => fun h x=>(priorAt (W:=W) (G:=G) (stage:=stage) (edge:=edge) (pick:=pick) (S:=S) (prior:=prior) (installed:=installed) (digits:=digits) (name:=name) h x).bind (rawRecord h)
/- Native comparisons happen on the old row, before the receiving venue is
consulted. Count and endpoint tests may discard any inactive or internalized role. -/
local notation "which" => parent_group W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp prior installed rank digits ports actual placed

include actual placed in
omit [DecidableEq I] in
private theorem both_groups (h : U) (e : live) (here : family e=digits.symm (band h)) (cross : kept e.val) :
    band ((cell) (src₀ e.val))=band h ∧ band ((cell) (dst₀ e.val))=band h := by
  let a:=firstSite (src₀ e.val)
  let b:=firstSite (dst₀ e.val)
  have diff : mergeHub flag k g (key a)≠mergeHub flag k g (key b):=fun eqn=>cross (Subtype.ext eqn)
  have native:=actual e
  have taken : ∀v ∈ ({key a,key b}:Finset _),digits (splitKey (mergeHub flag k g v)).1=band h:=by
    intro v mem
    have pair := Finset.mem_insert.mp mem
    rcases pair with rfl|last
    · have src:=DescentPacking.PackedMatch.Local.Stage.group_from_parent (width:=k) (g:=g) prior rank digits flag ((oldHost) e) (key a) (key b) (ports e)
          (fun no=>congrArg key (native.1 no)) native.2 diff _ (Or.inl rfl)
      exact by simpa only [Equiv.apply_symm_apply] using congrArg digits (src.symm.trans here)
    · have val:=Finset.mem_singleton.mp last
      subst v
      have dst:=DescentPacking.PackedMatch.Local.Stage.group_from_parent (width:=k) (g:=g) prior rank digits flag ((oldHost) e) (key a) (key b) (ports e)
          (fun no=>congrArg key (native.1 no)) native.2 diff _ (Or.inr rfl)
      exact by simpa only [Equiv.apply_symm_apply] using congrArg digits (dst.symm.trans here)
  exact ⟨(placed _).trans (taken (key a) (by simp)),(placed _).trans (taken (key b) (by simp))⟩

/-- The complete immutable-donor shelf follows from the physical pre-trim
role records and their mass readback. In particular, every positive register
is reconstructed as a specific original/arm/supply parent. -/
def shelf
    (massRead : ∀h e r,rawRecord h e=some r→
    r.weight.val=(if kept e.val then bitsAt e.val/q else 0))
    (endRead : ∀h e r,rawRecord h e=some r→
    Witness R (slot₀ e).1 r ((raster) ((cell) (src₀ e.val))) ((raster) ((cell) (dst₀ e.val))))
    (liveRead : ∀h (t : Local C₀ h),rawRecord h (donors h t)=some (nativeRow h t)) : Measured.Shelf C₀ R Z where
  issued:=readOld
  covers h t:=by
    change ((priorAt (W:=W) (G:=G) (stage:=stage) (edge:=edge) (pick:=pick) (S:=S) (prior:=prior) (installed:=installed) (digits:=digits) (name:=name) h (slot₀ (donors h t))).bind _)=_
    rw [priorAt_live (W:=W) (G:=G) (edge:=edge) (pick:=pick) (S:=S) (prior:=prior) (installed:=installed) (digits:=digits) (name:=name) (groupName:=groupName) h (donors h t) (which h t)]
    exact liveRead h t
  proper h x r seen paid:=by
    change ((priorAt (W:=W) (G:=G) (stage:=stage) (edge:=edge) (pick:=pick) (S:=S) (prior:=prior) (installed:=installed) (digits:=digits) (name:=name) h x).bind _)=some r at seen
    unfold priorAt at seen
    split at seen
    next found =>
      let e:=found.choose
      have hit : rawRecord h e=some r:=seen
      have weight:=massRead h e r hit
      have cross : kept e.val:=by by_contra no;rw [ite_eq_right no] at weight;omega
      rw [ite_eq_left cross] at weight
      have bits : 0<bitsAt e.val:=by
        by_contra! zero
        have eqn : bitsAt e.val=0:=by omega
        rw [eqn, Nat.zero_div] at weight
        exact (Nat.ne_of_gt paid) weight
      let u:(coarse).graph.Edge:=(parent W G pick z hz fit pack p key flag k g).symm ⟨e.val,cross⟩
      have positive : 0<(C₀).count u:=(positive W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready grain qp u).2 bits
      have groups:=both_groups (W:=W) (G:=G) (edge:=edge) (pair:=pair) (pick:=pick) (z:=z) (hz:=hz) (fit:=fit) (pack:=pack) (p:=p) (key:=key) (flag:=flag) (k:=k) (g:=g) (q:=q) (old:=old) (picked:=picked) (affected:=affected) (site:=site) (A:=A) (prior:=prior) (rank:=rank) (digits:=digits) (ports:=ports) (actual:=actual) (placed:=placed) h e found.choose_spec.1 cross
      refine ⟨u,positive,?_,?_,?_,?_⟩
      · have loc : (slot₀ e).1=x.1 := congrArg Prod.fst found.choose_spec.2
        have endpoint := endRead h e r hit
        rw [loc] at endpoint
        exact endpoint
      · intro same
        exact venue_injective_on_band hostVenue groups.1.symm same
      · intro same
        exact venue_injective_on_band hostVenue groups.2.symm same
      · intro ends pos
        exact found.choose_spec.2
    next =>simp at seen

end
end Hierarchy.DescentOrdinaryParentSupport

end OAI
