import OAI.ThreeFlat.RAM.HistoryShrinkGroups

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure BitLayout
open HistoryMotifJoin HistoryBoundedJoin HistoryBoundedBody HistoryJoinScan
open Diagonal.HistoryContraction BitNetwork.Ordered
open scoped Fin.CommRing BigOperators

noncomputable section
variable {W n h p : ℕ} {F : Type} {arity : Fin n → ℕ}
  (A : HistoryGatherBody.Layout) (group : Bool) (node : ℕ) (m : Memory W)
  (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i, Fin (arity i) → BitSource h p)

open scoped Classical
open private out from OAI.ThreeFlat.RAM.HistoryShrinkGroups
local notation "dest" => out A group node
local notation "qa" => copy A group node m N (h:=h) (p:=p)
local notation "B" => build A group node m (p:=p) (h:=h) (n:=n)
variable (id : ((Fin 3→Bool)→F)→ℕ)

def finish (id : ((Fin 3→Bool)→F)→ℕ) := (B).output (Tape.tape N wire id qa)
def joinTicks (id : ((Fin 3→Bool)→F)→ℕ) :=
   4+(HistoryMotifJoin.rows A W group).length*(2*(joinHeader A W group).binds+4)+(B).ticks (Tape.tape N wire id qa)

theorem emit_join (input : Reads A group node m N wire id) (geometry : Chart A group node m N wire id)
    (fresh : group=false→h=0) :
    let outMem:=finish A group node m N wire id
    (join A W group).Exec m outMem (joinTicks A group node m N wire id) ∧
      HistoryCompiledRows.Records id (glue N wire) (dest 0) outMem ∧
      ∀ j : Fin 4,outMem (dest 1+j.val)=((Info.mk (dest 0) p (glue N wire).cells (glue N wire).internal).words j:Word W) := by
  let read:=GroupRead.of_values A group m node p h n geometry.cursor geometry.ports geometry.free geometry.active
    geometry.dense geometry.size geometry.maskRoom ((by decide : 2<14).trans geometry.source.wide) geometry.infoRoom
  apply group_emit A group node m N wire id input geometry.layout geometry.ranges
    (physical_space A group node m N id geometry.capacity) geometry.headerReads read rfl rfl rfl
  · change (if group then h else 0)=h
    cases v:group
    · simpa [v] using (fresh v).symm
    · rfl
  · exact geometry.source
  · exact geometry.retained
  · exact geometry.hubFit


section Chronological
open Diagonal.HistoryMaskOrder
open scoped Classical

/-- The raw role selected by a dense party ordinal is the corresponding
physical-mask bit, including the case of repeated party placements. -/
theorem selected_role (mask : Fin A.party.parties→Prop)
    (live : A.party.motif<(HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3).val)
    (fit : A.party.motif<2^W)
    (bits : ∀ j : Fin A.party.parties,
      (HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 5).val.testBit j.val=decide (mask j)) :
    Fintype.card {j : Fin A.party.parties // selectedBit A m j.val}=Fintype.card {j // mask j} ∧
    ∀ i : Fin (Fintype.card {j // mask j}), role A m i.val=(order mask i).val.val := by
  have eqp : (fun j : Fin A.party.parties=>selectedBit A m j.val)=mask :=
    funext fun j=>propext (occupied_iff A mask live fit bits j)
  subst mask
  refine ⟨rfl,?_⟩
  intro i
  simp only [role,dite_eq_left i.isLt]

private theorem cast_mask_order {P Q : ℕ} (eq : P=Q) (mask : Fin Q→Prop) :
    ∃ card : Fintype.card {j : Fin P // mask (j.cast eq)}=Fintype.card {j //mask j},
      ∀ i : Fin (Fintype.card {j //mask j}),
        (order (fun j:Fin P=>mask (j.cast eq)) (i.cast card.symm)).val.val=(order mask i).val.val := by
  cases eq
  exact ⟨rfl,fun _=>rfl⟩

/-- The physical six raw party roles, including repeated placements at a site,
have exactly the increasing dense ordering in the geometric piece constructor. -/
theorem selected_six_roles (six : A.party.parties=6) (mask : Fin 6→Prop)
    (live : A.party.motif<(HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3).val)
    (bits : ∀ j : Fin 6,(HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 5).val.testBit j.val=decide (mask j)) :
    Fintype.card {j : Fin A.party.parties // selectedBit A m j.val}=Fintype.card {j //mask j} ∧
    ∀ i : Fin (Fintype.card {j //mask j}),role A m i.val=(order mask i).val.val := by
  obtain ⟨card,ord⟩:=cast_mask_order six mask
  have selected:=selected_role A m (fun j=>mask (j.cast six)) live (live.trans (HistoryGatherBody.wordAt m _ 3).isLt)
    (fun j=>bits (j.cast six))
  exact ⟨selected.1.trans card,fun i=>(selected.2 (i.cast card.symm)).trans (ord i)⟩

def cache (node slot roleNum : ℕ) (col : ℕ) := sourceBank A node group slot roleNum col

private theorem sourceBank_eq_of_role {g : Bool} {a b : ℕ} (slot col : ℕ) (same : g=true→a=b) :
    sourceBank A node g slot a col=sourceBank A node g slot b col := by
  cases g with
  | false => rfl
  | true => exact congrArg (fun r=>sourceBank A node true slot r col) (same rfl)

/-- Successive stages preserve each physically distinct selected root. The key is
the real raw slot number; outputs of other visited slots may modify scratch
registers, command tables, and all their own data. -/
def childData (i : Fin n) (k : ℕ) (state : Memory W) :=
  let cached:=cache A group node i.val k
  HistoryCompiledRows.Records id (N i) (cached 0) state ∧
  (∀ j : Fin 4,state (cached 1+j.val)=((Info.mk (cached 0) (arity i) (N i).cells (N i).internal).words j:Word W)) ∧
  (group=true → ∀ j : Fin (arity i),state (cached 2+j.val)=(sourceAddress (wire i j):Word W))

def childAddress (i : Fin n) (k x : ℕ) :=
  let cached:=cache A group node i.val k
  (cached 0≤x ∧ x<cached 0+4*(N i).cells) ∨ (cached 1≤x ∧ x<cached 1+4) ∨
    (group=true ∧ cached 2≤x ∧ x<cached 2+arity i)

theorem child_retain (i : Fin n) (k : ℕ) {μ ν : Memory W}
    (r : childData A group node N wire id i k μ)
    (keep : ∀ a,childAddress A group node N i k a→ν a=μ a) : childData A group node N wire id i k ν := by
  let cached:=cache A group node i.val k
  refine ⟨?_,?_,?_⟩
  · intro f j
    change ν (cached 0+(4*f.val+j.val))=_
    rw [keep _ (.inl (by
      change cached 0≤cached 0+(4*f.val+j.val) ∧ cached 0+(4*f.val+j.val)<cached 0+4*(N i).cells
      have:=f.isLt
      have:=j.isLt
      omega))]
    exact r.1 f j
  · intro j
    change ν (cached 1+j.val)=_
    rw [keep _ (.inr (.inl ⟨Nat.le_add_right (cached 1) j.val,Nat.add_lt_add_left j.isLt (cached 1)⟩))]
    exact r.2.1 j
  · intro live j
    change ν (cached 2+j.val)=_
    rw [keep _ (.inr (.inr ⟨live,Nat.le_add_right (cached 2) j.val,Nat.add_lt_add_left j.isLt (cached 2)⟩))]
    exact r.2.2 live j

/-- Reading all emitted child records and maps in the mount for the concluding join
uses only the row's own publication and separation from later raw-party writes. -/
theorem reads_after (limit : ℕ) (input : Memory W)
    (step : Memory W→ℕ→Memory W) (k : Fin n→Fin limit)
    (published : ∀ i,let pfx:=(List.range (k i).val).foldl step input
      childData A group node N wire id i (k i).val (step pfx (k i).val))
    (later : ∀ i (j : Fin limit),(k i).val<j.val→let pfx:=(List.range j.val).foldl step input
      ∀ x,childAddress A group node N i (k i).val x→step pfx j.val x=pfx x)
    (roles : ∀ i,group=true→ role A ((List.range limit).foldl step input) i.val=(k i).val)
    (identity : ∀ i (j : Fin (arity i)),group=false → sourceAddress (wire i j)=2+j.val) :
    Reads A group node ((List.range limit).foldl step input) N wire id := by
  let state (j : ℕ):=(List.range j).foldl step input
  have succ (j : ℕ) : state (j+1)=step (state j) j := by simp [state,List.range_succ]
  have keep (i : Fin n) (j : ℕ) (hj : j≤limit) (gt : (k i).val<j) :
    childData A group node N wire id i (k i).val (state j) := by
    induction j with
    | zero=>omega
    | succ j ih=>
      rw [succ]
      by_cases now:j=(k i).val
      · subst j;exact published i
      · have g:(k i).val<j:=by omega
        exact child_retain A group node N wire id i (k i).val (ih (by omega) g)
          (later i ⟨j,by omega⟩ g)
  have row (i : Fin n) := keep i limit le_rfl (k i).isLt
  have eq (i : Fin n) (b : ℕ) : sector A group node (state limit) i b =
      cache A group node i.val (k i).val b :=
    sourceBank_eq_of_role A node i.val b (roles i)
  refine ⟨?_,?_,?_,identity⟩
  · intro i
    rw [eq i 0]
    exact (row i).1
  · intro i j
    rw [eq i 1,eq i 0]
    exact (row i).2.1 j
  · intro i j yes
    rw [eq i 2]
    exact (row i).2.2 yes j

end Chronological

section PhysicalSite
open Diagonal Diagonal.MotifOuterTerms Diagonal.MotifKernel Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
variable {J E S H Z : Type} [Field F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Z] [DecidableEq Z] {k d r s c b : ℕ}
  (D : PortGraph J E) (G : Supply J S) (place : J→Z) (v : Z) (width base : E→ℕ) (sw : H→S→ℕ)
  (code : H ↪ Fin (2^k)) (letter : H≃Fin s) (z : Histogram H r) (edges : Fin b≃Absorbed (ports G) place v)
  (parts : Fin c≃{j // place j=v}) {e t : Fin c→ℕ} (sup : ∀ i,Fin (e i)≃(ports G).Port (parts i).val)
  (dem : ∀ i,Fin (t i)≃D.Port (parts i).val) (fit : ∀ i q j,sw q (sup i j).1.1≤d)
  (table : ∀ q j,D.State (fun a=>Fin (2^base a)) j→(ports G).State (fun a=>Fin (2^sw q a)) j→F)
  (comp : BitNetwork F ((r*d)+(r*d+r*d))) (cnt : BitNetwork F (r+(r+r)))
  (old : ∀ i,(a : D.Port (parts i).val)→Fin (width a.1.1)→BitSource (HistogramTileNetwork.order G place v sw z edges (k:=k)).bits p)
  (cross : (x : ExternalAt (ports G) place v)→Fin (histWidth sw z x.val.val+r*k)→Fin p)
local notation "childTree" => fun i=>Tree.party D G (parts i).val base (hd D base code parts dem i) (sup i) sw
  (fit i) table letter z comp cnt
local notation "nets" => fun i=>(childTree i).compile
local notation "wires" => localWire D G place v width base sw code z edges parts sup dem old cross
local notation "tree" => Tree.occupiedTree D G place v width base sw code letter z edges parts sup dem fit table comp cnt old cross

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Fintype Z] in
/-- The records published by the occupied-party join are the compiled node
used by the actual physical shrinkPiece. The selector and the trivalent rows
of each child are exactly those in the mathematical party tree. -/
theorem emit_occupied (input : Reads A true node m nets wires id) (geometry : Chart A true node m nets wires id) :
    let outMem:=finish A true node m nets wires id
    (join A W true).Exec m outMem (joinTicks A true node m nets wires id) ∧
    HistoryCompiledRows.Records id (tree).compile (resultBank A node true 0) outMem ∧
    ∀ j : Fin 4,outMem (resultBank A node true 1+j.val)=
      ((Info.mk (resultBank A node true 0) p (tree).compile.cells (tree).compile.internal).words j:Word W) :=
  emit_join A true node m nets wires id input geometry (by simp)

variable {U I Vtx : Type} [Fintype U] [Fintype I] [Fintype Vtx] [DecidableEq Vtx]
  (put : U→I→Vtx) (site : Vtx) (motifs : Fin n≃Active put site)
  (piece : ∀ _u : Active put site,Tree F p)
local notation "pieces" => fun i=>(piece (motifs i)).compile
local notation "pins" => fun (_:Fin n) (j:Fin p)=>(BitSource.pin j : BitSource 0 p)
local notation "assembled" => Tree.activeTree put site motifs piece

omit [Field F] [Fintype U] [Fintype I] [Fintype Vtx] [DecidableEq Vtx] in
/-- The physical outer join agrees with the native first-occurrence enumeration
of all active motifs. Its references to the child streams are taken from the
chronological S12 banks in that same order. -/
theorem emit_active (input : Reads A false node m pieces pins id) (geometry : Chart A false node m pieces pins id) :
    let outMem:=finish A false node m pieces pins id
    (join A W false).Exec m outMem (joinTicks A false node m pieces pins id) ∧
    HistoryCompiledRows.Records id (assembled).compile (resultBank A node false 0) outMem ∧
    ∀ j : Fin 4,outMem (resultBank A node false 1+j.val)=
      ((Info.mk (resultBank A node false 0) p (assembled).compile.cells (assembled).compile.internal).words j:Word W) :=
  emit_join A false node m pieces pins id input geometry (by simp)

end PhysicalSite

section Arm
variable {g : ℕ} (J : HistoryGatherBody.Layout) (P : HistoryGatherExecution.Plan W) (initial afterPair : Memory W)
  (pairSteps : ℕ) (child : BitNetwork F g) (mapping : Fin g→BitSource h p)

/-- Published data from an elected old party. The pair and map phases are deterministic;
writing the map is disjoint from the separately stored factor stream and its four-word info. -/
structure Elected : Prop where
  pair : (HistoryPartyPair.procedure W J.party).Exec initial afterPair pairSteps
  gather : (HistoryGatherBody.procedure W J).Exec afterPair (HistoryGatherExecution.output J P afterPair)
    (HistoryGatherExecution.tariff W J P)
  rows : HistoryCompiledRows.Records id child (HistoryPartyPair.atPair J.party node 0) (HistoryGatherExecution.output J P afterPair)
  info : ∀ k : Fin 4,(HistoryGatherExecution.output J P afterPair) (HistoryPartyPair.atPair J.party node 1+k.val)=
    ((Info.mk (HistoryPartyPair.atPair J.party node 0) g child.cells child.internal).words k:Word W)
  pins : ∀ j,(HistoryGatherExecution.output J P afterPair) (HistoryPartyPair.atPair J.party node 2+j.val)=
    (sourceAddress (mapping j):Word W)

theorem elected_gather
    (run : (HistoryPartyPair.procedure W J.party).Exec initial afterPair pairSteps)
    (records : HistoryCompiledRows.Records id child (HistoryPartyPair.atPair J.party node 0) afterPair)
    (header : ∀ k : Fin 4,afterPair (HistoryPartyPair.atPair J.party node 1+k.val)=
      ((Info.mk (HistoryPartyPair.atPair J.party node 0) g child.cells child.internal).words k:Word W))
    (gather : (HistoryGatherBody.procedure W J).Exec afterPair (HistoryGatherExecution.output J P afterPair)
      (HistoryGatherExecution.tariff W J P))
    (mapOk : ∀ j : Fin g,(HistoryGatherExecution.output J P afterPair)
      (HistoryPartyPair.atPair J.party node 2+j.val)=(sourceAddress (mapping j):Word W))
    (away : ∀ x,(HistoryPartyPair.atPair J.party node 0≤x ∧ x<HistoryPartyPair.atPair J.party node 0+4*child.cells) ∨
      (HistoryPartyPair.atPair J.party node 1≤x ∧ x<HistoryPartyPair.atPair J.party node 1+4) →
        (x<J.temp ∨ J.temp+(HistoryGatherBody.fields (W:=W) J).length≤x) ∧
        (∀ q j,j<HistoryGatherExecution.cap J q→x<HistoryGatherBody.srcBase J q j ∨ HistoryGatherBody.srcBase J q j+P.width q j≤x) ∧
        (x<P.gatherBase ∨ P.gatherBase+P.gatherCount≤x)) :
    Elected node id J P initial afterPair pairSteps child mapping := by
  have keep (x) (hx) := HistoryGatherExecution.output_away J P afterPair x (away x hx).1 (away x hx).2.1 (away x hx).2.2
  refine ⟨run,gather,?_,?_,mapOk⟩
  · intro r j;rw [keep _ (.inl (by have:=r.isLt;have:=j.isLt;omega))];exact records r j
  · intro j;rw [keep _ (.inr (by have:=j.isLt;omega))];exact header j

end Arm


end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks Computability.VPVNP.Compression
open Diagonal Diagonal.CompressorPacking Diagonal.HistoryContraction Diagonal.MotifKernel
open Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section

variable {c d Q p W : ℕ} {V H Tag L F : Type} [Field F] [Fintype F]
  [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c→ℕ) (code : Arc V H Tag L d c ↪ ℕ)
  (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L×Fin d)×Fin Q)
  (base : P.Motif→Fin 2→ℕ) (r : P.Motif→ℕ) (T : ∀m,FixedMotifTile demandGraph supplyGraph (base m) F)
  (x : Histories P base r T) (hn : ∀a : Tag,-a=a) (good : TagConditions P.slots (shift P) P.offset)
  (n : Fin 4→ℕ) (positive : ∀i,0<n i) (edgeOrder : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
  (padding : LiftedSlots (V×Tag) pad L) (site : Site V Tag L)

local notation "lay" => historyLayout P base r T x
local notation "outG" => outGraph P hn good lay n edgeOrder hc pad padding
local notation "outW" => outputWidth P base r T x hn good lay n edgeOrder hc pad

open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryRefreshEmitter
variable {Dmax : ℕ}

section
open scoped Fin.CommRing
open private sitePins from OAI.ThreeFlat.Diagonal.ShrinkSiteTree
open private gatherShrinkAt from OAI.ThreeFlat.RAM.HistoryGatherExecution

attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph SlotRefinement.actualWidth allPieceSlots

set_option maxHeartbeats 600000 in
private abbrev emitPartyAt :=
  fun (choice : Bool)
    (old : (i : {i // P.placement choice i = site}) →
      (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
    (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
      (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)
    (m : P.Motif) (part : {u // partySite P choice m u=site})
    (layout : HistoryGatherBody.Layout) (node incident archiveArity : ℕ) (input : Memory W)
    (heightFit : siteHeight (r m) (T m).bitCap≤Dmax) =>
  letI := (T m).hasLetter
  let J:HistoryGatherBody.Layout:={layout with party:={layout.party with motif:=incident,party:=part.val.val}}
  let t : Fin (Dmax+1):=⟨siteHeight (r m) (T m).bitCap,by omega⟩
  let dp:=(Fintype.equivFin (demandGraph.Port part.val)).symm
  let sp:=(Fintype.equivFin (supplyGraph.Port part.val)).symm
  let B : Diagonal.HistogramTileNetwork.Header (demandGraph.Port part.val) (T m).Alphabet (fun q=>(base m) q.1.1)
      (T m).bits (Fintype.card (demandGraph.Port part.val)):=⟨dp,(T m).encode⟩
  let alphabet:=Fintype.equivFin (T m).Alphabet
  let hdrGood:=headerGood ShrinkMotif.supply part.val sp B.code
  let letter:=headerLetter ShrinkMotif.supply part.val sp alphabet B.code
  let z:=numberHistogram alphabet (x m)
  let tbl:=tile demandGraph ShrinkMotif.supply part.val (base m) B sp (T m).output (fun z a=>(T m).output_le_cap z _) (T m).entry
  let sc:=MotifNativeCompactors.partialInput F (r m) t.val
  let pc:=MotifNativeCompactors.partialInput F (r m*(T m).bitCap) t.val
  let checks:=admission hdrGood letter sc z
  let body:=tiled tbl pc
  let place:=partySite P choice m
  let owned:=HistoryMaskOrder.order (fun e=>wireOwner supplyGraph.tail supplyGraph.head place e=some site)
  let priv:=HistogramTileNetwork.order (k:=(T m).bits) ShrinkMotif.supply place site (T m).output (x m) owned
  let cross:=crossingPin (p:=p) P base r T x hn good choice n positive edgeOrder hc pad padding site new m
  let oi:=oldPinSource (h:=priv.bits) P w code hQ num choice site old m part.val
  let fi:=priv.partySource cross part
  let wire:=partyPointer demandGraph ShrinkMotif.supply part.val (base m) (demandWidth P w num m) B sp (T m).output (x m) oi fi
  fun (tp:B.arity+(Fintype.card (supplyGraph.Port part.val)*(T m).bitCap+Fintype.card (supplyGraph.Port part.val)*(T m).bitCap)≤archiveArity)
      (cp:Fintype.card (supplyGraph.Port part.val)*(T m).bits+Fintype.card (T m).Alphabet≤archiveArity) readC readP room=>
  let post:=electedOutput tbl hdrGood letter tp cp J.party node input t z readC readP
  let pcost:=electedCost tbl hdrGood letter tp cp J.party input t z readC readP
  have pr:=elected_arm tbl hdrGood letter tp cp J.party node input t z readC readP room
  let data:=HistoryGatherExecution.typedSources (W:=W) J demandGraph ShrinkMotif.supply part.val (base m)
    (demandWidth P w num m) B sp (T m).output (x m) oi fi
  let basePtr:=((HistoryGatherBody.selected J post).privatePage 2).val
  let word:=HistoryGatherExecution.gatheredWord (W:=W) basePtr (fun i=>BitLayout.sourceAddress (wire i))
  let plan:=HistoryGatherExecution.nativePlan J post data word
  fun page ar initial active copies nst est digitBound pos resident headerBound fits mapCount mapRoom range hdr
      keep pageClear headAddress digit scalar supWidth demWidth oldRoom newRoom demand supply atNode addressFit roomMap=>
  have mapped:=gatherShrinkAt (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
    site choice old new m part layout incident post page ar initial active copies nst est digitBound pos resident headerBound fits mapCount
      mapRoom range hdr keep pageClear headAddress digit scalar supWidth demWidth oldRoom newRoom demand supply
  have ptr:=HistoryRefreshEmitter.private_map_base J node post atNode addressFit
  have bits : ∀ j,HistoryGatherExecution.output J plan post (HistoryPartyPair.atPair J.party node 2+j.val)=
      (BitLayout.sourceAddress (wire j):Word W) := by
    intro j;rw [←ptr];exact mapped.2 j
  have info (j : Fin 4) : post (HistoryPartyPair.atPair J.party node 1+j.val)=
    (HistoryBoundedJoin.Info.words ⟨HistoryPartyPair.atPair J.party node 0,
      r m * (Fintype.card (supplyGraph.Port part.val) * (T m).bits) +
        (r m * B.arity + Fintype.card (supplyGraph.Port part.val) * (r m * (T m).bitCap)),
      (pair checks body).compile.cells,
      (pair checks body).compile.internal⟩ j:Word W) := by
    simp only [HistoryContraction.Tree.compiled_rows,HistoryContraction.Tree.compiled_bits,
      HistoryContraction.Tree.pair_rows,HistoryContraction.Tree.pair_bits]
    dsimp only [post,HistoryRefreshEmitter.electedOutput,checks,body,sc,pc]
    exact pr.2.1 j
  elected_gather node (HistoryRefreshEmitter.tag (K:=F)) J plan input post pcost
    (pair checks body).compile wire pr.1 pr.2.2 info mapped.1 bits roomMap

/-- Native checks, payload, paired result and geometric map for an actual
occupied side of a shrinkPiece. The declarations of the register pages and
the individual visible port words are those of the two ROM readers. -/
abbrev emit_party :=
  emitPartyAt (p:=p) (W:=W) (Dmax:=Dmax) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
    site (historyLayout P base r T x)

end

/-- The actual paired publisher used in `emit_party` preserves the external state.
The three resource bounds are respectively the number of children, the compiled
row count and the total number of LUT/compactor argument slots. -/
abbrev emit_party_away {u : ℕ} :=
  fun (m : P.Motif) (part : {v // partySite P lay m v=site})
    (layout : HistoryGatherBody.Layout) (node incident archiveArity : ℕ) (input : Memory (16*u^10))
    (heightFit : siteHeight (r m) (T m).bitCap≤Dmax) =>
  letI := (T m).hasLetter
  let J:HistoryGatherBody.Layout:={layout with party:={layout.party with motif:=incident,party:=part.val.val}}
  let t : Fin (Dmax+1):=⟨siteHeight (r m) (T m).bitCap,by omega⟩
  let dp:=(Fintype.equivFin (demandGraph.Port part.val)).symm
  let sp:=(Fintype.equivFin (supplyGraph.Port part.val)).symm
  let B : Diagonal.HistogramTileNetwork.Header (demandGraph.Port part.val) (T m).Alphabet (fun q=>(base m) q.1.1)
      (T m).bits (Fintype.card (demandGraph.Port part.val)):=⟨dp,(T m).encode⟩
  let alphabet:=Fintype.equivFin (T m).Alphabet
  let hdrGood:=headerGood ShrinkMotif.supply part.val sp B.code
  let letter:=headerLetter ShrinkMotif.supply part.val sp alphabet B.code
  let z:=numberHistogram alphabet (x m)
  let tbl:=tile demandGraph ShrinkMotif.supply part.val (base m) B sp (T m).output (fun z a=>(T m).output_le_cap z _) (T m).entry

  let issued := fun (tp:B.arity+(Fintype.card (supplyGraph.Port part.val)*(T m).bitCap+Fintype.card (supplyGraph.Port part.val)*(T m).bitCap)≤archiveArity)
      (cp:Fintype.card (supplyGraph.Port part.val)*(T m).bits+Fintype.card (T m).Alphabet≤archiveArity)
      readC readP room loc count gates pins=>
    HistoryRefreshEmitter.elected_room_away (u:=u) tbl hdrGood letter tp cp J.party node input t z
      readC readP room loc count gates pins
  issued

abbrev emit_party_outsideNode {u : ℕ} :=
  fun (m : P.Motif) (part : {v // partySite P lay m v=site})
    (layout : HistoryGatherBody.Layout) (node incident archiveArity : ℕ) (input : Memory (16*u^10))
    (heightFit : siteHeight (r m) (T m).bitCap≤Dmax) =>
  let issued := fun tp cp readC readP room loc count gates pins addr safe=>
    emit_party_away (Q:=Q) (Dmax:=Dmax) (u:=u) P base r T x site m part layout node incident archiveArity input heightFit
      tp cp readC readP room loc count gates pins addr (HistoryRefreshEmitter.PartyAway.of_outside loc safe)
  issued

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure BitLayout
open HistoryMotifJoin HistoryBoundedJoin HistoryBoundedBody HistoryJoinScan
open Diagonal.HistoryContraction BitNetwork.Ordered
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {F : Type} {W p n h : ℕ} {arity : Fin n→ℕ} {A : HistoryGatherBody.Layout}
    (node : ℕ) (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ)


section Roster
open private before_range from OAI.ThreeFlat.RAM.HistoryRefreshRoot
variable [Field F] [Fintype F]

/-- Runtime scratch states for the elected branches. The unused rows below run the
actual zero-sized batch, pair and gather, including all their physical writes. -/
structure ArmRows (A : HistoryGatherBody.Layout) (W n : ℕ) where
  select : ℕ→Option (Fin n)
  index : Fin n→Fin A.party.parties
  at_index : ∀ i,select (index i).val=some i
  pairOut : Fin n→Memory W
  plan : Fin n→HistoryGatherExecution.Plan W
  pairCost : Fin n→ℕ

variable (Z : ArmRows A W n)
namespace ArmRows
def pairOutAt (j : ℕ) (input : Memory W) := match Z.select j with
  | none=>HistoryRefreshEmitter.afterVacantPair (withParty A j).party node id input
  | some i=>Z.pairOut i

def mapOutAt (j : ℕ) (pairOut : Memory W) := match Z.select j with
  | none=>HistoryRefreshEmitter.vacantMap (withParty A j) pairOut
  | some i=>HistoryGatherExecution.output (withParty A j) (Z.plan i) pairOut

def advance (input : Memory W) (j : ℕ) := Z.mapOutAt j (Z.pairOutAt node id j input)

def entry (initial : Memory W) (j : ℕ) := (List.range j).foldl (Z.advance node id) initial

def ticks (initial : Memory W) (j : ℕ) := match Z.select j with
  | none=>HistoryRefreshEmitter.vacantPairCost (withParty A j) (Z.entry node id initial j)
  | some i=>Z.pairCost i

def mapTicks (j : ℕ) := match Z.select j with
  | none=>HistoryRefreshEmitter.vacantMapCost (withParty A j) W
  | some i=>HistoryGatherExecution.tariff W (withParty A j) (Z.plan i)

variable (initial : Memory W)
local notation "atSlot" => Z.entry node id initial
local notation "step" => Z.advance node id

omit [Fintype F] [Field F] in
/-- Construct the physical input chart of the finishing join and execute all
raw-party procedures from the images of the actual elected and unused arms. -/
theorem emit (elected : ∀ (j : Fin A.party.parties) (i : Fin n),Z.select j.val=some i →
      Elected node id (withParty A j.val) (Z.plan i) (atSlot j.val) (Z.pairOut i) (Z.pairCost i) (N i) (wire i))
    (vacant : ∀ j : Fin A.party.parties,Z.select j.val=none →
      HistoryRefreshEmitter.VacantRoom (withParty A j.val) node id (atSlot j.val))
    (later : ∀ i (j : Fin A.party.parties),(Z.index i).val<j.val → ∀ a,
      childAddress A true node N i (Z.index i).val a → step (atSlot j.val) j.val a=atSlot j.val a)
    (roles : ∀ i,role A (atSlot A.party.parties) i.val=(Z.index i).val) :
    Reads A true node (atSlot A.party.parties) N wire id ∧
      ∀ before j tail,List.range A.party.parties=before++j::tail →
        let mid:=before.foldl step initial
        (HistoryPartyPair.procedure W (withParty A j).party).Exec mid (Z.pairOutAt node id j mid) (Z.ticks node id initial j) ∧
        (HistoryGatherBody.procedure W (withParty A j)).Exec (Z.pairOutAt node id j mid) (step mid j) (Z.mapTicks j) := by
  constructor
  · apply reads_after A true node N wire id A.party.parties initial step Z.index
    · intro i
      have on:=Z.at_index i
      have q:=elected (Z.index i) i on
      have get : step (atSlot (Z.index i).val) (Z.index i).val=
          HistoryGatherExecution.output (withParty A (Z.index i).val) (Z.plan i) (Z.pairOut i):=by
        simp [advance,pairOutAt,mapOutAt,on]
      change childData A true node N wire id i (Z.index i).val (step (atSlot (Z.index i).val) (Z.index i).val)
      rw [get]
      exact ⟨q.rows,q.info,fun _=>q.pins⟩
    · exact later
    · exact fun i _=>roles i
    · simp
  · intro before j tail eqn
    obtain ⟨rfl,hj⟩:=before_range eqn
    change (HistoryPartyPair.procedure W (withParty A j).party).Exec (atSlot j)
      (Z.pairOutAt node id j (atSlot j)) (Z.ticks node id initial j) ∧
      (HistoryGatherBody.procedure W (withParty A j)).Exec (Z.pairOutAt node id j (atSlot j))
        (step (atSlot j) j) (Z.mapTicks j)
    cases choice:Z.select j with
    | none=>
      have run:=HistoryRefreshEmitter.vacant_arm (withParty A j) node id (atSlot j) (vacant ⟨j,hj⟩ choice)
      simpa [advance,pairOutAt,mapOutAt,ticks,mapTicks,choice] using run
    | some i=>
      have run:=elected ⟨j,hj⟩ i choice
      simp only [advance,pairOutAt,mapOutAt,ticks,mapTicks,choice]
      exact ⟨run.pair, run.gather⟩

omit [Fintype F] [Field F] in
/-- One physical motif, including its private prefix initialization, every raw arm
and the typed occupied-party join. -/
theorem motif (input : Memory W) (first : initial=headerImage (privateHeader A W) A.privateStarts 9 input)
    (space : A.privateStarts+9<2^W) (safe : HistoryPartyBatchExec.Protected (privateHeader A W) input A.privateStarts 9)
    (elected : ∀ (j : Fin A.party.parties) (i : Fin n),Z.select j.val=some i →
      Elected node id (withParty A j.val) (Z.plan i) (atSlot j.val) (Z.pairOut i) (Z.pairCost i) (N i) (wire i))
    (vacant : ∀ j : Fin A.party.parties,Z.select j.val=none →
      HistoryRefreshEmitter.VacantRoom (withParty A j.val) node id (atSlot j.val))
    (later : ∀ i (j : Fin A.party.parties),(Z.index i).val<j.val → ∀ a,
      childAddress A true node N i (Z.index i).val a → step (atSlot j.val) j.val a=atSlot j.val a)
    (roles : ∀ i,role A (atSlot A.party.parties) i.val=(Z.index i).val)
    (geometry : Chart A true node (atSlot A.party.parties) N wire id) :
    let m:=atSlot A.party.parties
    let out:=finish A true node m N wire id
    (HistoryMotifJoin.motif A W).Exec input out (4+9*(2*(privateHeader A W).binds+4)+
      ((List.range A.party.parties).map (fun j=>Z.ticks node id initial j+Z.mapTicks j)).sum+joinTicks A true node m N wire id) ∧
      HistoryCompiledRows.Records id (glue N wire) (resultBank A node true 0) out ∧
      ∀ j : Fin 4,out (resultBank A node true 1+j.val)=
        ((Info.mk (resultBank A node true 0) p (glue N wire).cells (glue N wire).internal).words j:Word W) := by
  subst initial
  obtain ⟨read,loops⟩:=Z.emit node N wire id _ elected vacant later roles
  obtain ⟨joined,stored⟩:=emit_join A true node _ N wire id read geometry (by simp)
  exact ⟨motif_exec A input space safe _ _ _ _ loops _ _ joined,stored⟩
end ArmRows
end Roster

section SiteRun
open HistoryPartyBatchExec
open private before_range from OAI.ThreeFlat.RAM.HistoryRefreshRoot
variable [Field F] [Fintype F]

/-- One roster entry for the native bounded incidence loop. In the genuine
incidence prefix its joined network is the corresponding shrinkPiece. The
unused suffix has an empty raw-party selection. -/
structure SiteSlot (F : Type) (W p : ℕ) (A : HistoryGatherBody.Layout) where
  shared : ℕ
  count : ℕ
  arity : Fin count→ℕ
  children : ∀ i,BitNetwork F (arity i)
  wire : ∀ i,Fin (arity i)→BitSource shared p
  arms : ArmRows A W count

namespace SiteSlot
variable (Z : SiteSlot F W p A)
def init (_ : SiteSlot F W p A) (input : Memory W) := headerImage (privateHeader A W) A.privateStarts 9 input
def joined : BitNetwork F p := glue Z.children Z.wire

def endState (input : Memory W) :=
  let before:=Z.arms.entry node id (Z.init input) A.party.parties
  finish A true node before Z.children Z.wire id

def cost (input : Memory W) :=
  let first:=Z.init input
  let before:=Z.arms.entry node id first A.party.parties
  4+9*(2*(privateHeader A W).binds+4)+
    ((List.range A.party.parties).map (fun j=>Z.arms.ticks node id first j+Z.arms.mapTicks j)).sum+
    joinTicks A true node before Z.children Z.wire id

variable (input : Memory W)
local notation "first" => Z.init input
local notation "atArm" => Z.arms.entry node id first
local notation "step" => Z.arms.advance node id

structure Live : Prop where
  prefixRoom : A.privateStarts+9<2^W
  prefixSafe : Protected (privateHeader A W) input A.privateStarts 9
  elected : ∀ (j : Fin A.party.parties) (i : Fin Z.count),Z.arms.select j.val=some i →
    Elected node id (withParty A j.val) (Z.arms.plan i) (atArm j.val) (Z.arms.pairOut i)
      (Z.arms.pairCost i) (Z.children i) (Z.wire i)
  vacant : ∀ j : Fin A.party.parties,Z.arms.select j.val=none →
    HistoryRefreshEmitter.VacantRoom (withParty A j.val) node id (atArm j.val)
  later : ∀ i (j : Fin A.party.parties),(Z.arms.index i).val<j.val → ∀ a,
    childAddress A true node Z.children i (Z.arms.index i).val a → step (atArm j.val) j.val a=atArm j.val a
  roles : ∀ i,role A (atArm A.party.parties) i.val=(Z.arms.index i).val
  geometry : Chart A true node (atArm A.party.parties) Z.children Z.wire id

omit [Fintype F] [Field F] in
theorem run (live : Z.Live node id input) :
    (HistoryMotifJoin.motif A W).Exec input (Z.endState node id input) (Z.cost node id input) ∧
    HistoryCompiledRows.Records id Z.joined (resultBank A node true 0) (Z.endState node id input) ∧
    ∀ j : Fin 4,(Z.endState node id input) (resultBank A node true 1+j.val)=
      ((Info.mk (resultBank A node true 0) p Z.joined.cells Z.joined.internal).words j:Word W) :=
  Z.arms.motif node Z.children Z.wire id first input rfl live.prefixRoom live.prefixSafe
    live.elected live.vacant live.later live.roles live.geometry
end SiteSlot

structure SiteRun (F : Type) (W p : ℕ) (A : HistoryGatherBody.Layout) where
  slot : (i : ℕ)→Memory W→SiteSlot F W p (withMotif A i)

namespace SiteRun
variable (Z : SiteRun F W p A) (first : Memory W)
def takeSlot (m : Memory W) (i : ℕ) := (Z.slot i m).endState node id m
def entry (i : ℕ) := (List.range i).foldl (Z.takeSlot node id) first
def slotCost (i : ℕ) := (Z.slot i (Z.entry node id first i)).cost node id (Z.entry node id first i)
local notation "atSlot" => Z.entry node id first
local notation "final" => atSlot A.party.motifs
variable (pieces : Fin n→BitNetwork F p)
local notation "pins" => fun (_ : Fin n) (j : Fin p)=>(BitSource.pin j : BitSource 0 p)

def endState := finish A false node final pieces pins id
def cost (prefixCost : ℕ) := prefixCost+((List.range A.party.motifs).map (Z.slotCost node id first)).sum+
  joinTicks A false node final pieces pins id

omit [Fintype F] [Field F] in
/-- Actual whole shrinking kernel. Its S12 stream equals the ordered local
product of the physical incidence roster. Only the active prefix appears
in the joined trivalent network. -/
theorem emit_site (S : Diagonal.CompressorPacking.Native.Graph.Stage) (mode : A.mode=.shrink S)
    (oldCap : ℕ) (input : Memory W)
    (beginRun : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input first
      (4+(oldCap+1)*(2*(HeaderScan.closed (w:=W) (HistoryMotifJoin.childPrefix A.nodePorts oldCap)).binds+4)))
    (size : n≤A.party.motifs) (live : ∀ j : Fin A.party.motifs,(Z.slot j.val (atSlot j.val)).Live node id (atSlot j.val))
    (correct : ∀ i : Fin n,(Z.slot i.val (atSlot i.val)).joined=pieces i)
    (later : ∀ i : Fin n,∀ j : Fin A.party.motifs,i.val<j.val → ∀ a,
      childAddress A false node pieces i i.val a → Z.takeSlot node id (atSlot j.val) j.val a=atSlot j.val a)
    (geometry : Chart A false node final pieces pins id) :
    let charge:=4+(oldCap+1)*(2*(HeaderScan.closed (w:=W) (HistoryMotifJoin.childPrefix A.nodePorts oldCap)).binds+4)
    let out:=Z.endState node id first pieces
    (kernelProcedure A W oldCap).Exec input out (Z.cost node id first pieces charge) ∧
    HistoryCompiledRows.Records id (glue pieces pins) (resultBank A node false 0) out ∧
      ∀ j : Fin 4,out (resultBank A node false 1+j.val)=
        ((Info.mk (resultBank A node false 0) p (glue pieces pins).cells (glue pieces pins).internal).words j:Word W) := by
  dsimp only
  have rows (i : Fin A.party.motifs):=(Z.slot i.val (atSlot i.val)).run node id (atSlot i.val) (live i)
  have read : Reads A false node final pieces pins id := by
    apply reads_after A false node pieces pins id A.party.motifs first (Z.takeSlot node id) (Fin.castLE size)
    · intro i
      have a:=rows (Fin.castLE size i)
      have eqn:=correct i
      refine ⟨eqn ▸ a.2.1,?_,by simp⟩
      intro j
      change (Z.slot i.val (atSlot i.val)).endState node id (atSlot i.val)
        (resultBank (withMotif A i.val) node true 1+j.val)=
          ((Info.mk (resultBank (withMotif A i.val) node true 0) p
            (pieces i).cells (pieces i).internal).words j:Word W)
      rw [←eqn]
      exact a.2.2 j
    · exact later
    · simp
    · intro i j _; rfl
  obtain ⟨j,store⟩:=emit_join A false node final pieces pins id read geometry (by simp)
  refine ⟨kernel_shrink A S mode oldCap input first _ beginRun (fun j m=>Z.takeSlot node id m j)
    (Z.slotCost node id first) ?_ _ _ j,store⟩
  intro pre i tail loc
  obtain ⟨rfl,lt⟩:=before_range loc
  exact (rows ⟨i,lt⟩).1
end SiteRun
end SiteRun

/-- Match the native join tree constructor itself. Dependent arities and private
wire assignments therefore coincide with the tree in the mathematical contraction. -/
structure Children {F : Type} {p : ℕ} (tree : Tree F p) where
  shared : ℕ
  count : ℕ
  arity : Fin count→ℕ
  wire : ∀ i,Fin (arity i)→BitSource shared p
  factor : ∀ i,Tree F (arity i)
  eqn : tree=.join shared count arity wire factor

def Children.join {F : Type} {p : ℕ} (h n : ℕ) (ar : Fin n→ℕ)
    (wire : ∀i,Fin (ar i)→BitSource h p) (factor : ∀i,Tree F (ar i)) :
    Children (Tree.join h n ar wire factor) := ⟨h,n,ar,wire,factor,rfl⟩

def Children.slot {F : Type} {p W : ℕ} {tree : Tree F p} {A : HistoryGatherBody.Layout}
    (C : Children tree) (arms : ArmRows A W C.count) : SiteSlot F W p A :=
  ⟨C.shared,C.count,C.arity,fun i=>(C.factor i).compile,C.wire,arms⟩

theorem Children.joined {F : Type} {p W : ℕ} {tree : Tree F p} {A : HistoryGatherBody.Layout}
    (C : Children tree) (arms : ArmRows A W C.count) : (C.slot arms).joined=tree.compile := by
  rcases C with ⟨_,_,_,_,_,rfl⟩
  rfl

section Mask
variable (A : HistoryGatherBody.Layout) (active : Fin A.party.parties→Prop)
local notation "ord" => Diagonal.HistoryMaskOrder.order active

/-- Inverse of the six-party mask order. The ordinal of a physically vacant
party is absent, including all parties of a padded motif row. -/
def maskSelect (j : ℕ) : Option (Fin (Fintype.card {k // active k})) :=
  if bound : j<A.party.parties then
    if on : active ⟨j,bound⟩ then some ((ord).symm ⟨⟨j,bound⟩,on⟩) else none
  else none

def maskArms (out : Fin (Fintype.card {k // active k})→Memory W)
    (plan : Fin (Fintype.card {k // active k})→HistoryGatherExecution.Plan W)
    (cost : Fin (Fintype.card {k // active k})→ℕ) : ArmRows A W (Fintype.card {k // active k}) where
  select := maskSelect A active
  index i := (ord i).val
  at_index i := by simp [maskSelect,(ord i).val.isLt,(ord i).property]
  pairOut := out
  plan := plan
  pairCost := cost

theorem maskSelect_some {j : ℕ} {i : Fin (Fintype.card {k // active k})}
    (selected : maskSelect A active j=some i) : (ord i).val.val=j := by
  unfold maskSelect at selected
  split at selected
  · split at selected
    · cases selected;rw [Equiv.apply_symm_apply]
    · contradiction
  · contradiction

/-- Each present raw party has its own native paired output and gather plan.
Their values can depend on the scratch memory left by its predecessor. -/
structure ArmWrite (W : ℕ) where
  paired : Memory W
  plan : HistoryGatherExecution.Plan W
  ticks : ℕ

variable [Field F] [Fintype F]
/-- Semantic value of the elected arm on its own input memory. The proof
records both the paired output and the private map as one program execution. -/
structure ArmWrite.Real (u node : ℕ) (id : ((Fin 3→Bool)→F)→ℕ)
    (J : HistoryGatherBody.Layout) {ar h p : ℕ} (net : BitNetwork F ar)
    (wire : Fin ar→BitSource h p) (input : Memory W) (z : ArmWrite W) : Prop where
  elected : Elected node id J z.plan input z.paired z.ticks net wire
  width : ∀ side k,k<HistoryGatherExecution.cap J side→z.plan.width side k≤J.party.V
  mapBase : z.plan.gatherBase=HistoryPartyPair.atPair J.party node 2
  mapWords : z.plan.gatherCount≤J.party.V
  pairFrame : ∀ a,HistoryRefreshEmitter.PartyAway u J.party node a→z.paired a=input a

variable (put : (i : Fin (Fintype.card {k // active k}))→Memory W→ArmWrite W)

def maskedStep (mem : Memory W) (j : ℕ) : Memory W :=
  match maskSelect A active j with
  | none=>HistoryRefreshEmitter.vacantPass (withParty A j) node id mem
  | some i=>let write:=put i mem
            HistoryGatherExecution.output (withParty A j) write.plan write.paired

def maskedBefore (start : Memory W) (j : ℕ) : Memory W :=
  (List.range j).foldl (maskedStep node id A active put) start

def evaluatedArms (start : Memory W) : ArmRows A W (Fintype.card {k // active k}) :=
  let atArm i:=put i (maskedBefore node id A active put start (ord i).val.val)
  maskArms A active (fun i=>(atArm i).paired) (fun i=>(atArm i).plan) (fun i=>(atArm i).ticks)

omit [Field F] [Fintype F] in
theorem evaluatedArms_entry (start : Memory W) (j : ℕ) :
    (evaluatedArms node id A active put start).entry node id start j =
      maskedBefore node id A active put start j := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [ArmRows.entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (evaluatedArms node id A active put start).advance node id
      ((evaluatedArms node id A active put start).entry node id start j) j=_
    rw [ih]
    simp only [maskedBefore,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    let m:=maskedBefore node id A active put start j
    change (evaluatedArms node id A active put start).advance node id m j=maskedStep node id A active put m j
    cases sel : maskSelect A active j with
    | none=>simp only [ArmRows.advance,ArmRows.pairOutAt,ArmRows.mapOutAt,evaluatedArms,maskArms,sel,
        maskedStep,HistoryRefreshEmitter.vacantPass]
    | some i=>
      have num:=maskSelect_some A active sel
      simp only [ArmRows.advance,ArmRows.pairOutAt,ArmRows.mapOutAt,evaluatedArms,maskArms,sel,
        maskedStep,num,m]

end Mask

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks Computability.VPVNP.Compression
open Diagonal Diagonal.CompressorPacking Diagonal.HistoryContraction Diagonal.MotifKernel
open Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section

open private sitePins pieceAt from OAI.ThreeFlat.Diagonal.ShrinkSiteTree
attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph SlotRefinement.actualWidth allPieceSlots
set_option maxRecDepth 16000

variable {c d Q p W : ℕ} {V H Tag L F : Type} [Field F] [Fintype F]
  [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c→ℕ) (code : Arc V H Tag L d c ↪ ℕ)
  (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L×Fin d)×Fin Q)
  (base : P.Motif→Fin 2→ℕ) (r : P.Motif→ℕ) (T : ∀m,FixedMotifTile demandGraph supplyGraph (base m) F)
  (x : Histories P base r T) (hn : ∀a : Tag,-a=a) (good : TagConditions P.slots (shift P) P.offset)
  (n : Fin 4→ℕ) (positive : ∀i,0<n i) (edgeOrder : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
  (padding : LiftedSlots (V×Tag) pad L) (site : Site V Tag L)

local notation "lay" => historyLayout P base r T x
local notation "pieceFn" => pieceAt (F:=F) (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site

set_option maxHeartbeats 1000000 in
private def childrenAt (choice : Bool)
    (old : (i : {i // P.placement choice i=site}) → (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
    (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
      (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)
    (m : P.Motif) : Children (F:=F) (p:=p) (pieceFn choice old new m) := by
  letI := (T m).hasLetter
  unfold pieceAt Tree.occupiedTree
  exact Children.join (F:=F) (p:=p) _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- Actual arities, child networks and source maps are read from the constructor
of the particular geometric shrinkPiece. No equality of unrelated histories is used. -/
def pieceChildren :=
  childrenAt (F:=F) (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site lay

section
variable (choice : Bool)
  (old : (i : {i // P.placement choice i=site}) → (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
  (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
    (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)

local notation "kids" => childrenAt (F:=F) (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new
local notation "arityCount" => fun m : P.Motif => Fintype.card {j // partySite P choice m j=site}

set_option maxHeartbeats 1000000 in
omit [Fintype F] in
private theorem childrenCountAt (m : P.Motif) : (kids m).count=arityCount m := by
  let childCount : Tree F p → ℕ
    | .atom _ => 0
    | .join _ count _ _ _ => count
  have native := congrArg childCount (kids m).eqn
  change childCount (pieceFn choice old new m) = (kids m).count at native
  let roles : Fin (childCount (pieceFn choice old new m)) ≃
      {j // partySite P choice m j=site} :=
    HistoryMaskOrder.order (fun j => partySite P choice m j=site)
  exact native.symm.trans ((Fintype.card_fin _).symm.trans (Fintype.card_congr roles))

private def slotAt (m : P.Motif) (A : HistoryGatherBody.Layout) (arms : ArmRows A W (arityCount m)) :
    SiteSlot F W p A :=
  Children.slot (tree:=pieceFn choice old new m) (A:=A) (W:=W) (kids m)
    (cast (congrArg (ArmRows A W)
      (childrenCountAt (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
        site choice old new m).symm) arms)

private def compiledAt (m : P.Motif) : BitNetwork F p :=
  Tree.compile (p:=p) (F:=F) (pieceFn choice old new m)

local notation "slotHere" => slotAt (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new
local notation "treeHere" => compiledAt (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new

set_option maxHeartbeats 1000000 in
omit [Fintype F] in
private theorem slotSharedAt (m : P.Motif) (A : HistoryGatherBody.Layout) (arms : ArmRows A W (arityCount m)) :
    (slotHere m A arms).shared=∑ i,historyWidth P base r T x m
      ((Diagonal.HistoryMaskOrder.order (fun e=>wireOwner supplyGraph.tail supplyGraph.head
        (partySite P choice m) e=some site)) i).val := rfl

omit [Fintype F] in
private theorem slotJoinedAt (m : P.Motif) (A : HistoryGatherBody.Layout) (arms : ArmRows A W (arityCount m)) :
    (slotHere m A arms).joined=treeHere m := by
  unfold slotAt compiledAt
  exact Children.joined (tree:=pieceFn choice old new m) (A:=A) (W:=W) (kids m) _
end

def pieceSlot :=
  slotAt (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site lay

omit [Fintype F] in
/-- The shared pins of the compiled geometric piece are exactly the widths
issued for the local absorbed edges in the public eight-edge order. -/
theorem pieceSlot_shared : type_of% (slotSharedAt (p:=p) (W:=W) P w code hQ num base r T x hn good n
    positive edgeOrder hc pad padding site lay) :=
  slotSharedAt (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site lay

omit [Fintype F] in
theorem pieceSlot_joined : type_of% (slotJoinedAt (p:=p) (W:=W) P w code hQ num base r T x hn good n
    positive edgeOrder hc pad padding site lay) :=
  slotJoinedAt (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site lay

/-- At the first valid incidence there is an actual motif. All unoccupied
extra physical rows take a zero-child group join whose fields are ignored. -/
def emptySlot (A : HistoryGatherBody.Layout) : SiteSlot F W p A where
  shared := 0
  count := 0
  arity := Fin.elim0
  children i := i.elim0
  wire i := i.elim0
  arms := ⟨fun _=>none, Fin.elim0, fun i=>Fin.elim0 i, Fin.elim0, Fin.elim0, Fin.elim0⟩

variable {s : ℕ} (enum : Fin s≃Active (partySite P lay) site)
  (A : HistoryGatherBody.Layout)
  (roster : ∀ i : Fin s,Memory W→ArmRows (HistoryMotifJoin.withMotif A i.val) W
    (Fintype.card {j // partySite P lay (enum i).val j=site}))

private def selectedSiteAt (choice : Bool)
    (old : (i : {i // P.placement choice i=site}) → (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
    (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
      (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)
    {s : ℕ} (enum : Fin s≃Active (partySite P choice) site) (A : HistoryGatherBody.Layout)
    (roster : ∀ i : Fin s,Memory W→ArmRows (HistoryMotifJoin.withMotif A i.val) W
      (Fintype.card {j // partySite P choice (enum i).val j=site})) : SiteRun F W p A where
  slot j mem := if live : j<s then
    slotAt (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new
      (enum ⟨j,live⟩).val _ (roster ⟨j,live⟩ mem) else emptySlot _

def selectedSite :=
  selectedSiteAt (p:=p) (W:=W) (s:=s) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site lay

set_option maxHeartbeats 1400000 in
omit [Fintype F] in
private theorem selectedPieceAt (choice : Bool)
    (old : (i : {i // P.placement choice i=site}) → (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
    (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
      (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)
    {s : ℕ} (enum : Fin s ≃ Active (partySite P choice) site) (A : HistoryGatherBody.Layout)
    (roster : ∀ i : Fin s, Memory W → ArmRows (HistoryMotifJoin.withMotif A i.val) W
      (Fintype.card {j // partySite P choice (enum i).val j=site})) (i : Fin s) (mem : Memory W) :
    ((selectedSiteAt (F:=F) (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
      site choice old new enum A roster).slot i.val mem).joined =
      compiledAt (F:=F) (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
        site choice old new (enum i).val := by
  simp only [selectedSiteAt,dite_eq_left i.isLt]
  exact slotJoinedAt (F:=F) (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
    site choice old new (enum i).val _ (roster i mem)

local notation "selectedPieceResult" => selectedPieceAt (F:=F) (p:=p) (W:=W)
  P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site lay

omit [Fintype F] in
theorem selectedPiece : type_of% selectedPieceResult := selectedPieceResult

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
