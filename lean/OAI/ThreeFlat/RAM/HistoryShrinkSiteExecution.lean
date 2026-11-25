import OAI.ThreeFlat.RAM.HistoryShrinkPlacement

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open private oldLocal previous_page rows_fit from OAI.ThreeFlat.RAM.HistoryShrinkPlacement
open private out from OAI.ThreeFlat.RAM.HistoryShrinkGroups
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr Diagonal.TickWorkspace
open HistoryStageBody.Physical HistoryScratch HistoryMotifJoin HistoryGatherBody
open Diagonal.HistoryContraction HistoryRefreshEmitter BitNetwork.Ordered
open scoped BigOperators Fin.CommRing

noncomputable section
variable {F : Type} [Field F] [Fintype F] {W p u n : ℕ} {A : HistoryGatherBody.Layout}
  (node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ)

namespace SiteSlot
variable (Z : SiteSlot F W p A) (input : Memory W)
local notation "first" => Z.init input
local notation "atArm" => Z.arms.entry node id first

omit [Field F] [Fintype F] in
/-- The complete current motif, including the finishing copy tape, leaves every
previously completed motif's local stream and header intact. -/
theorem endState_previous (banks : PhysicalBanks u A) (live : Z.Live node id input)
    (arms : Z.ArmSpace node id input u) {x : ℕ} {loc : Local} (old : PageRead A node x loc)
    (prior : loc.motif≠A.party.motif+2) : Z.endState node id input x=input x := by
  have C:=live.geometry.capacity
  have early:=old.below banks C.nodeBound C.sectors
  have s14:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<18)
  have begin_ : first x=input x:=by
    have off : ¬(A.privateStarts≤x ∧ x<A.privateStarts+9) := by rw [banks.privateStarts];omega
    change HistoryMotifJoin.headerImage _ A.privateStarts 9 input x=_
    simp [HistoryMotifJoin.headerImage,fillSegment,off]
  have armsPreserve (k : ℕ) (bound : k≤A.party.parties) : atArm k x=input x := by
    induction k with
    | zero=>exact begin_
    | succ k ih=>
      let j : Fin A.party.parties:=⟨k,by omega⟩
      have next : atArm (k+1)=Z.arms.advance node id (atArm k) k := by
        simp only [ArmRows.entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [next]
      exact (Z.advance_previous node id input banks C arms j (live.vacant j) old (.inl prior)).trans (ih (by omega))
  apply Eq.trans _ (armsPreserve A.party.parties le_rfl)
  apply finish_away A true node (atArm A.party.parties) Z.children Z.wire id banks live.geometry x (.inl early)
  · intro j
    have address := rootLoc A true node j.val
    dsimp only [out] at address
    rw [address]
    apply old.apart C.sectors _ (parentLocal_valid A true node (atArm A.party.parties) Z.children id C j)
    exact fun same=>prior (congrArg Local.motif same)
  · intro i
    rw [childLoc A true node (atArm A.party.parties) i 3]
    apply old.apart C.sectors _ (childLocal_valid A true node (atArm A.party.parties) Z.children id C i 3)
    exact fun same=>prior (congrArg Local.motif same)

end SiteSlot

namespace SiteRun
variable (Z : SiteRun F W p A) (first : Memory W) (pieces : Fin n→BitNetwork F p)
local notation "atSlot" => Z.entry node id first
local notation "pins" => fun (_ : Fin n) (j : Fin p)=>(BitSource.pin j : BitSource 0 p)

omit [Field F] [Fintype F] in
/-- This is the between-motif input of `SiteRun.emit_site`. It follows from sector
disjointness even at a vacant raw motif and does not assume any earlier output equality. -/
theorem later (banks : PhysicalBanks u A)
    (live : ∀ j : Fin A.party.motifs,(Z.slot j.val (atSlot j.val)).Live node id (atSlot j.val))
    (arms : ∀ j : Fin A.party.motifs,(Z.slot j.val (atSlot j.val)).ArmSpace node id (atSlot j.val) u)
    (geometry : Chart A false node (atSlot A.party.motifs) pieces pins id)
    (i : Fin n) (j : Fin A.party.motifs) (lt : i.val<j.val) (x : ℕ)
    (word : childAddress A false node pieces i i.val x) :
    Z.takeSlot node id (atSlot j.val) j.val x=atSlot j.val x := by
  have C:=geometry.capacity
  have four : 4≤A.party.V := by
    have cap:=C.sectors
    nlinarith only [cap,Nat.zero_le (A.party.motifs*A.party.parties)]
  obtain ⟨col,old⟩:=previous_page A false node pieces i i.val x word (by simp) (by simp)
    (fun _=>lt.trans j.isLt) (rows_fit (A:=A) pieces C.cells i) (C.demand i) four
  let J:=withMotif A j.val
  have resident : PageRead J node x (oldLocal A false i.val i.val col.val):=⟨old.valid,old.lower,old.upper⟩
  apply (Z.slot j.val (atSlot j.val)).endState_previous node id (atSlot j.val) (banks.withMotif j.val)
    (live j) (arms j) resident
  change i.val+2≠j.val+2
  omega

end SiteRun
end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks Computability.VPVNP.Compression
open Diagonal Diagonal.CompressorPacking Diagonal.HistoryContraction Diagonal.MotifKernel
open Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open HistoryMotifJoin HistoryPartyBatchExec HistoryBoundedJoin HistoryStageBody.Physical
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {c d Q p W : ℕ} {V H Tag L F : Type} [Field F] [Fintype F]
  [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c→ℕ) (code : Arc V H Tag L d c ↪ ℕ)
  (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L×Fin d)×Fin Q)
  (base : P.Motif→Fin 2→ℕ) (r : P.Motif→ℕ) (T : ∀m,FixedMotifTile demandGraph supplyGraph (base m) F)
  (x : Histories P base r T) (hn : ∀a : Tag,-a=a) (good : TagConditions P.slots (shift P) P.offset)
  (n : Fin 4→ℕ) (positive : ∀i,0<n i) (edgeOrder : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
  (padding : LiftedSlots (V×Tag) pad L) (site : Site V Tag L)

open private sitePins pieceAt from OAI.ThreeFlat.Diagonal.ShrinkSiteTree
open private selectedSiteAt selectedPieceAt from OAI.ThreeFlat.RAM.HistoryShrinkArms
attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph SlotRefinement.actualWidth allPieceSlots

section Run
variable {u s : ℕ} (A : HistoryGatherBody.Layout) (run : SiteRun F W p A)
    (factors : Fin s → Tree F p) (node : ℕ) (id : ((Fin 3 → Bool) → F) → ℕ) (first : Memory W)
local notation "pieces" => (fun i : Fin s => (factors i).compile)
local notation "atSlot" => run.entry node id first
local notation "pins" => (fun (_ : Fin s) (j : Fin p) => (BitSource.pin j : BitSource 0 p))
local notation "root" => (Tree.join 0 s (fun _ => p) pins factors : Tree F p)

omit [Fintype F] [Field F] in
private theorem executeSiteRun
    (correct : ∀ i : Fin s, (run.slot i.val (atSlot i.val)).joined = pieces i)
    (banks : PhysicalBanks u A)
    (S : Native.Graph.Stage) (mode : A.mode=.shrink S) (oldCap : ℕ) (input : Memory W)
    (cap : oldCap≤A.party.V)
    (begun : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input first
      (4+(oldCap+1)*(2*(HeaderScan.closed (w:=W) (childPrefix A.nodePorts oldCap)).binds+4)))
    (begins : first=fillSegment A.nodePorts.starts (oldCap+1)
      (fun a=>(childWidth A.nodePorts oldCap (numeric input) a:Word W)) input)
    (size : s≤A.party.motifs)
    (live : ∀ j : Fin A.party.motifs,(run.slot j.val (atSlot j.val)).Live node id (atSlot j.val))
    (arms : ∀ j : Fin A.party.motifs,(run.slot j.val (atSlot j.val)).ArmSpace node id (atSlot j.val) u)
    (geometry : Chart (W:=W) (F:=F) (n:=s) (h:=0) (p:=p) (arity:=fun _ : Fin s => p)
      A false node (atSlot A.party.motifs) pieces pins id) :
    let charge:=4+(oldCap+1)*(2*(HeaderScan.closed (w:=W) (childPrefix A.nodePorts oldCap)).binds+4)
    let out:=SiteRun.endState (n:=s) (Z:=run) node id first pieces
    (kernelProcedure A W oldCap).Exec input out (SiteRun.cost (n:=s) (Z:=run) node id first pieces charge) ∧
    HistoryCompiledRows.Records id (root).compile (resultBank A node false 0) out ∧
    (∀ j : Fin 4,out (resultBank A node false 1+j.val)=
      ((Info.mk (resultBank A node false 0) p (root).compile.cells (root).compile.internal).words j:Word W)) ∧
    ∀ a,OutsideNode u node a→ out a=input a := by
  dsimp only
  have within := SiteRun.later (n:=s) (Z:=run) node id first pieces banks live arms geometry
  obtain ⟨go, rows, info⟩ := SiteRun.emit_site (n:=s) (Z:=run) node id first pieces S mode oldCap input
    begun size live correct within geometry
  exact ⟨go, rows, info, SiteRun.endState_outsideNode (n:=s) (Z:=run) node id first pieces
    banks oldCap input cap begins live arms geometry⟩
end Run

section Selected
variable {u s : ℕ} (choice : Bool)
    (old : (i : {i // P.placement choice i=site}) → (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
    (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
      (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)
    (enum : Fin s ≃ Active (partySite P choice) site) (A : HistoryGatherBody.Layout)
    (roster : ∀ i : Fin s, Memory W → ArmRows (withMotif A i.val) W
      (Fintype.card {j // partySite P choice (enum i).val j=site}))
    (node : ℕ) (id : ((Fin 3 → Bool) → F) → ℕ) (first : Memory W)

local notation "selectedRun" => selectedSiteAt (F:=F) (p:=p) (W:=W) (s:=s)
  P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new enum A roster
local notation "factorAt" => pieceAt (F:=F) (p:=p)
  P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new
local notation "pieceRow" => selectedPieceAt (F:=F) (p:=p) (W:=W) (s:=s)
  P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new enum A roster
local notation "selectedKernel" => executeSiteRun (u:=u) (s:=s) (W:=W) (p:=p) (F:=F)
  A selectedRun (fun i : Fin s => factorAt (enum i).val) node id first
  (fun i : Fin s => pieceRow i (SiteRun.entry (Z:=selectedRun) node id first i.val))

set_option maxHeartbeats 1400000 in
omit [Fintype F] in
private theorem executeSelectedLayout : type_of% selectedKernel := selectedKernel
end Selected

variable {u s : ℕ}

local notation "shrinkKernel" => executeSelectedLayout (F:=F) (p:=p) (W:=W) (u:=u) (s:=s)
  P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site (historyLayout P base r T x)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1400000 in
omit [Fintype F] in
/-- The chronological shrink kernel, its root Info, all trivalent rows and the
outside-node frame refer to the very same execution and the geometric shrinkSite. -/
theorem execute_shrinkSite : type_of% shrinkKernel := shrinkKernel

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
