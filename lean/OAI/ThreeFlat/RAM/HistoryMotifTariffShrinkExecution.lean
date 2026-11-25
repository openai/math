import OAI.ThreeFlat.Diagonal.HistoryMotifTariffGather
import OAI.ThreeFlat.RAM.HistoryMotifTariffShrinkParty
import OAI.ThreeFlat.RAM.HistorySelectedFrame
import OAI.ThreeFlat.Diagonal.ShrinkWordRoot

namespace OAI
/-! # Native shrink execution for the physical motif tariff -/

set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks Computability.VPVNP.Compression
open Diagonal Diagonal.CompressorPacking Diagonal.HistoryContraction Diagonal.MotifKernel
open Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section

set_option maxRecDepth 16000

/-- The finite port shapes of a recorded piece, indexed by the number of
active parties. The arities are exposed at this precise numerical domain. -/
private structure TariffChildren {F : Type} {p : ℕ} (tree : Tree F p) (n : ℕ) where
  shared : ℕ
  arity : Fin n → ℕ
  wire : ∀ i, Fin (arity i) → BitSource shared p
  factor : ∀ i, Tree F (arity i)
  eqn : tree = .join shared n arity wire factor

private abbrev TariffChildren.count {F : Type} {p n : ℕ} {tree : Tree F p} (_ : TariffChildren tree n) := n

private def TariffChildren.native {F : Type} {p n : ℕ} {tree : Tree F p}
    (C : TariffChildren tree n) : Children tree :=
  ⟨C.shared, n, C.arity, C.wire, C.factor, C.eqn⟩

private def Children.withCount {F : Type} {p : ℕ} {tree : Tree F p}
    (C : Children tree) (n : ℕ) (h : C.count = n) : TariffChildren tree n where
  shared := C.shared
  arity i := C.arity (i.cast h.symm)
  wire i := C.wire (i.cast h.symm)
  factor i := C.factor (i.cast h.symm)
  eqn := by
    subst n
    exact C.eqn

open private recordedRoleCount from OAI.ThreeFlat.RAM.HistoryShrinkIncidentRecords

private theorem roleCardEq (mask : Fin 6 → Prop) (inst : Fintype {j // mask j}) :
    @Fintype.card _ inst = recordedRoleCount mask :=
  congrArg (fun t : Fintype {j // mask j} => @Fintype.card _ t)
    (Subsingleton.elim inst (Subtype.fintype mask))

private theorem recordedRoleCount_le_six (mask : Fin 6 → Prop) : recordedRoleCount mask ≤ 6 := by
  classical
  let : Fintype {j // mask j} := Subtype.fintype mask
  calc
    recordedRoleCount mask = Fintype.card {j // mask j} := (roleCardEq mask inferInstance).symm
    _ ≤ Fintype.card (Fin 6) := Fintype.card_subtype_le mask
    _ = 6 := Fintype.card_fin 6

private def tariffRosterRows {A : HistoryGatherBody.Layout} {W : ℕ} (mask : Fin 6 → Prop)
    (inst : Fintype {j // mask j}) (arms : ArmRows A W (recordedRoleCount mask)) :
    ArmRows A W (@Fintype.card _ inst) :=
  cast (congrArg (ArmRows A W) (roleCardEq mask inst).symm) arms

private theorem Children.withCount_slot {F : Type} {p W : ℕ} {tree : Tree F p} {A : HistoryGatherBody.Layout}
    (C : Children tree) {k n : ℕ} (h : C.count = k) (e : k = n) (arms : ArmRows A W n) :
    C.slot (cast (congrArg (ArmRows A W) h.symm) (cast (congrArg (ArmRows A W) e.symm) arms)) =
      (C.withCount n (h.trans e)).native.slot arms := by
  subst k
  subst n
  rfl

open private sitePins pieceAt from OAI.ThreeFlat.Diagonal.ShrinkSiteTree
open private childrenAt childrenCountAt slotAt selectedSiteAt from OAI.ThreeFlat.RAM.HistoryShrinkArms
attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph SlotRefinement.actualWidth allPieceSlots

variable {c d Q p W : ℕ} {V H Tag L F : Type} [Field F] [Fintype F]
  [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c→ℕ) (code : Arc V H Tag L d c ↪ ℕ)
  (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L×Fin d)×Fin Q)
  (base : P.Motif→Fin 2→ℕ) (r : P.Motif→ℕ) (T : ∀m,FixedMotifTile demandGraph supplyGraph (base m) F)
  (x : Histories P base r T) (hn : ∀a : Tag,-a=a) (good : TagConditions P.slots (shift P) P.offset)
  (n : Fin 4→ℕ) (positive : ∀i,0<n i) (edgeOrder : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
  (padding : LiftedSlots (V×Tag) pad L) (site : Site V Tag L)

variable (choice : Bool)
    (old : (i : {i // P.placement choice i=site}) → (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
    (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
      (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)

local notation "pieceHere" => pieceAt (F:=F) (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new
local notation "childrenAtLayout" => childrenAt (F:=F) (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new
local notation "countAtLayout" => childrenCountAt (F:=F) (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new

set_option maxHeartbeats 1000000 in
private def tariffPieceChildren (m : P.Motif) :
    TariffChildren (pieceHere m) (recordedRoleCount (fun j => partySite P choice m j=site)) :=
  (childrenAtLayout m).withCount _ ((countAtLayout m).trans (roleCardEq _ _))

set_option maxHeartbeats 1000000 in
omit [Fintype F] in
private theorem tariffPieceSlot (m : P.Motif) (A : HistoryGatherBody.Layout)
    (arms : ArmRows A W (recordedRoleCount (fun j => partySite P choice m j=site))) :
    slotAt (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new m A
        (tariffRosterRows (fun j => partySite P choice m j=site) _ arms) =
      (tariffPieceChildren (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding site choice old new m).native.slot arms :=
  Children.withCount_slot (childrenAtLayout m) (countAtLayout m) (roleCardEq _ _) arms

section SelectedTariff
variable {k : ℕ} (enum : Fin k ≃ Active (partySite P choice) site) (A : HistoryGatherBody.Layout)
  (rows : ∀ i : Fin k, Memory W → ArmRows (HistoryMotifJoin.withMotif A i.val) W
    (recordedRoleCount (fun j => partySite P choice (enum i).val j=site)))

set_option maxHeartbeats 1000000 in
private def tariffSelectedSite : SiteRun F W p A :=
  selectedSiteAt (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
    site choice old new enum A (fun i m => tariffRosterRows (fun j => partySite P choice (enum i).val j=site) _ (rows i m))

set_option maxHeartbeats 1000000 in
omit [Fintype F] in
private theorem tariffSelectedOccupied (i : Fin k) (m : Memory W) :
    (tariffSelectedSite (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
      site choice old new enum A rows).slot i.val m =
    (tariffPieceChildren (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
      site choice old new (enum i).val).native.slot (rows i m) := by
  simp only [tariffSelectedSite, selectedSiteAt, dite_eq_left i.isLt]
  exact tariffPieceSlot (p:=p) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
    site choice old new (enum i).val _ (rows i m)

end SelectedTariff

private def tariffIssuedSlot {F : Type} [Field F] [Fintype F] {p W u node : ℕ} {tree : Tree F p}
    (id : ((Fin 3 → Bool) → F) → ℕ) (A : HistoryGatherBody.Layout) (mask : Fin A.party.parties → Prop)
    (C : TariffChildren tree (Fintype.card {j // mask j})) (rate : Fin (Fintype.card {j // mask j}) → ℕ)
    (m : Memory W) : SiteSlot F W p A :=
  issuedSlot (u:=u) (node:=node) id A mask C.arity (fun j => (C.factor j).compile) C.wire rate m

private def tariffIssuedRows {F : Type} [Field F] [Fintype F] {p W u node : ℕ} {tree : Tree F p}
    (id : ((Fin 3 → Bool) → F) → ℕ) (A : HistoryGatherBody.Layout) (mask : Fin A.party.parties → Prop)
    (C : TariffChildren tree (Fintype.card {j // mask j})) (rate : Fin (Fintype.card {j // mask j}) → ℕ)
    (m : Memory W) : ArmRows A W (Fintype.card {j // mask j}) :=
  (tariffIssuedSlot (u:=u) (node:=node) id A mask C rate m).arms

private theorem tariffIssuedSlot_eq {F : Type} [Field F] [Fintype F] {p W u node : ℕ} {tree : Tree F p}
    (id : ((Fin 3 → Bool) → F) → ℕ) (A : HistoryGatherBody.Layout) (mask : Fin A.party.parties → Prop)
    (C : TariffChildren tree (Fintype.card {j // mask j})) (rate : Fin (Fintype.card {j // mask j}) → ℕ)
    (m : Memory W) :
    C.native.slot (tariffIssuedRows (u:=u) (node:=node) id A mask C rate m) =
      tariffIssuedSlot (u:=u) (node:=node) id A mask C rate m := rfl

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Diagonal Diagonal.PhysicalStage
open Diagonal.CompressorPacking Diagonal.CompressorPacking.PhysicalShrink
open Diagonal.CompressorPacking.Native Diagonal.CompressorPacking.Native.ShrinkStage
open Diagonal.HistoryContraction Diagonal.NavigationPass Diagonal.ShrinkStageNav
open HistoryStageBody.Physical HistoryMotifJoin HistoryRefreshEmitter
open scoped Classical BigOperators Fin.CommRing
open private selected_bundle_positive from OAI.ThreeFlat.Diagonal.ShrinkSelectedGeometry
open private copiesPositive selectedSiteDecidableEq from OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply

open private colors_le from OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
open private recordedOutgoingGraph recordedOutgoingWidth from OAI.ThreeFlat.RAM.HistoryShrinkPartyRecords
open RAM.NavigationNodeRows
open private descriptorAllocation from OAI.ThreeFlat.RAM.HistoryShrinkArchive
noncomputable section
variable {F Pins : Type} [Field F] [Fintype F] (B : Block F) (level : Fin B.levels)
  (u start height K rem : ℕ)
local notation "W" => (16*u^10)
local notation "s" => B.exponent level.val
local notation "D" => 2^B.exponent (level.val+1)
local notation "d" => (2^s:ℕ)
local notation "t" => Diagonal.CompressorPacking.tagBits d
local notation "S" => shrinkStage s D
local notation "f" => shrinkFamily B start height level
local notation "J" => layout u (archive B start height K) f
local notation "reference" => kernelTemplate (shrinkGrid B level)
local notation "encode" => (HistoryRefreshEmitter.tag (K:=F))
variable (hD : 0 < 2^(B.exponent (level.val+1)))
  (small : let degree : ℕ := 2^(B.exponent level.val)
    ((2^(2*degree+1)*degree*degree : ℕ) : ℝ) / ((2^(B.exponent (level.val+1)) : ℕ) : ℝ) ≤ 1/1024)
  (A : State (2^(B.exponent level.val)) (shrinkCharge (B.exponent level.val)+rem))
attribute [local instance 2000] selectedSiteDecidableEq
local instance (priority := 2000) tariffRecordedBaseDecidableEq :
    DecidableEq (shrinkRecordState (B.exponent level.val) rem A).Base := Classical.decEq _
open private recordedRoleCount from OAI.ThreeFlat.RAM.HistoryShrinkIncidentRecords

local notation "M" => shrinkBinary B.shrink s D rem hD small A
local notation "X" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
local notation "hc" => colors_le s
local notation "oldWidth₀" => shrinkRecordWidth s rem A
local notation "rawCode" => Demand.key P (baseNat (X).order)
local notation "numbers" => motifNumbers P rawCode hc
local notation "baseWidth" => PhysicalShrink.widths B.shrink P oldWidth₀ (shrinkRecordCode s rem A) hc
local notation "many" => shrinkRecordCopies B.shrink s rem A
local notation "entries" => shrinkRecordTile B.shrink s rem A
local notation "valid" => Ordered.binaryPacking_conditions (X).order.symm (X).graph
local notation "edgeOrd" => edgeOrder P (baseNat (X).order) (tagOrdinal t).toEmbedding (S).pieces (S).pieceRadix (shrinkPieceBound s D)
local notation "pad" => PhysicalShrink.padding (2*d+1) d D
variable (branch : Fin (shrinkBinary B.shrink (B.exponent level.val) (2^(B.exponent (level.val+1))) rem hD small A).rules.count)
  (gt : 0 < Diagonal.CompressorPacking.tagBits (2^(B.exponent level.val)))
local notation "hist" => shrinkIssuedBranch B.shrink s D rem hD small A branch
local notation "lay" => ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
local notation "extra" => tagPadding (V:=(X).Base) (L:=BitWord rem) (tagOne gt) (tagOne_ne gt) pad
local notation "Gnew" => CompressorRefresh.union (shrinkingGraph P lay (S).pieces edgeOrd hc binary_neg valid) extra
local notation "wnew" => outputWidth P baseWidth many entries hist binary_neg valid lay (S).pieces edgeOrd hc pad
variable (previous : WordLayout (oldGraph (shrinkRecordPacking (B.exponent level.val) rem A))
    (shrinkRecordWidth (B.exponent level.val) rem A) Pins)
  (successor : let exponent := B.exponent level.val
    let nextDegree := 2^(B.exponent (level.val+1))
    let issuedLayout := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink exponent nextDegree rem hD small A branch)
    WordLayout (recordedOutgoingGraph exponent nextDegree rem A issuedLayout gt)
      (recordedOutgoingWidth B exponent nextDegree rem hD small A branch) Pins)
  (v : Computability.VPVNP.Compression.Site (shrinkRecordState (B.exponent level.val) rem A).Base
    (BitWord (Diagonal.CompressorPacking.tagBits (2^(B.exponent level.val)))) (BitWord rem))
  (order : let exponent := B.exponent level.val
    let nextDegree := 2^(B.exponent (level.val+1))
    let issuedLayout := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink exponent nextDegree rem hD small A branch)
    Incidents.SiteOrder («S»:=shrinkStage exponent nextDegree) (shrinkRecordPacking exponent rem A)
      (shrinkRecordState exponent rem A).order issuedLayout v (16*u^10))
variable (node : ℕ)
local notation "count" => (Incidents.siteKeys («S»:=S) (w:=W) P (X).order lay v).length
local notation "children" => fun _ : Computability.VPVNP.Compression.Site (X).Base (BitWord t) (BitWord rem)=>d*2^(2*d+1)
local notation "childOrder" => Owner.childOrder P lay
local notation "old" => WordLayout.oldPin previous successor ((P).placement lay) children childOrder v
local notation "new_" => WordLayout.newPin previous successor ((P).placement lay) children childOrder v
local notation "treeArgs" => tariffPieceChildren (F:=F) («p»:=WordLayout.argSize previous successor ((P).placement lay) children childOrder v) P oldWidth₀ rawCode (selected_bundle_positive s) numbers
  baseWidth many entries hist binary_neg valid (S).pieces (copiesPositive s D hD small) edgeOrd hc pad extra v lay old new_
local notation "piece" => shrinkPiece P oldWidth₀ rawCode (selected_bundle_positive s) numbers
  baseWidth many entries hist binary_neg valid (S).pieces (copiesPositive s D hD small) edgeOrd hc pad extra v old new_
local notation "siteTree" => shrinkSite P oldWidth₀ rawCode (selected_bundle_positive s) numbers
  baseWidth many entries hist binary_neg valid (S).pieces (copiesPositive s D hD small) edgeOrd hc pad extra v old new_ order.equiv
local notation "row" i:arg => (order.equiv i).val
local notation "active" i:arg => fun j : Fin 6=>partySite P lay (row i) j=v
local notation "roles" i:arg => HistoryMaskOrder.order (active i)
local notation "tileNo" i:arg => RefreshDemandRows.tileNumber
  (PhysicalShrink.b P oldWidth₀ (shrinkRecordCode s rem A) hc (row i)) (B.shrink.base ∘ B.shrink.row)
local notation "party" i:arg j:arg => shrinkParty B.shrink (tileNo i) ((roles i) j).val

set_option maxHeartbeats 1000000 in
/-- The actual finite tariff attached to the selected grid cell and its numerical
party. Both charges read the multiplicity of this very incidence. -/
def recordedAllowance (i : Fin count) (j : Fin (recordedRoleCount (active i))) : ℕ :=
  partyRate (party i j)*(W+1)^3*(1+many (row i)) + partyMapRate reference (party i j)*(1+many (row i))

local notation "rate" => recordedAllowance B level u rem hD small A branch v order
local notation "cloud" i:arg => withMotif J (Fin.val i)
local notation "bundle" i:arg => treeArgs (row i)
local notation "nets" i:arg => fun j=>((bundle i).factor j).compile
local notation "slot" i:arg m:arg => tariffIssuedSlot (F:=F) («W»:=W)
  (u:=u) (node:=node) encode (cloud i) (active i) (bundle i) (rate i) m

set_option maxHeartbeats 1400000 in
private def recordedIssuedRows (i : Fin count) (m : Memory W) :
    ArmRows (cloud i) W (recordedRoleCount (active i)) :=
  tariffIssuedRows (F:=F) («W»:=W) (u:=u) (node:=node) encode (cloud i) (active i) (bundle i) (rate i) m

local notation "issuedRows" i:arg m:arg =>
  recordedIssuedRows B level u start height K rem hD small A branch gt previous successor v order node i m

open private selectedSiteAt from OAI.ThreeFlat.RAM.HistoryShrinkArms

set_option maxHeartbeats 1400000 in
/-- The physical roster determined by the recorded shrink. In each occupied
row the choice of an achieved pair is evaluated on the prefix memory of its raw party. -/
def recordedSite : SiteRun F W (WordLayout.argSize previous successor ((P).placement lay) children childOrder v) J :=
  tariffSelectedSite (F:=F) («p»:=WordLayout.argSize previous successor ((P).placement lay) children childOrder v)
    («W»:=W) P oldWidth₀ rawCode (selected_bundle_positive s) numbers baseWidth many
    entries hist binary_neg valid (S).pieces (copiesPositive s D hD small) edgeOrd hc pad extra v lay old new_
    order.equiv J (fun i m => issuedRows i m)

local notation "run" => recordedSite B level u start height K rem hD small A branch gt previous successor v order node

set_option maxHeartbeats 1400000 in
theorem recordedSite_occupied (i : Fin count) (m : Memory W) :
    (run).slot i.val m=slot i m :=
  (tariffSelectedOccupied (F:=F) («p»:=WordLayout.argSize previous successor ((P).placement lay) children childOrder v)
    («W»:=W) P oldWidth₀ rawCode (selected_bundle_positive s) numbers baseWidth many
    entries hist binary_neg valid (S).pieces (copiesPositive s D hD small) edgeOrd hc pad extra v lay old new_
    order.equiv J (fun k state => issuedRows k state) i m).trans
    (tariffIssuedSlot_eq (F:=F) («W»:=W) (u:=u) (node:=node) encode (cloud i) (active i) (bundle i) (rate i) m)

set_option maxHeartbeats 1400000 in
theorem recordedSite_padding {i : ℕ} (after : count ≤ i) (m : Memory W) :
    (run).slot i m=emptySlot (withMotif J i) := by
  simp only [recordedSite, tariffSelectedSite, selectedSiteAt, dite_eq_right (Nat.not_lt.mpr after)]


open Diagonal.TickWorkspace HistoryPartyBatchExec
local notation "V₁" => volume u
local notation "p" => WordLayout.argSize previous successor ((P).placement lay) children childOrder v
local notation "cap" => (f).childBound
variable (input : Memory (16*u^10))
local notation "first" => fillSegment (J).nodePorts.starts (cap+1)
  (fun a=>(childWidth (J).nodePorts cap (numeric input) a:Word W)) input
local notation "atSlot" => (run).entry node encode first
local notation "st" i:arg => (run).slot (Fin.val i) (atSlot (Fin.val i))

/-- Native words available at the beginning of each incidence loop. Earlier
node rows and the original geometry can still be read, together with the
just-issued prefix for every real child of the current node. -/
structure SiteRead (u node «cap» : ℕ) (N : HistoryNodePorts.Layout)
    (input m : Memory (16*u^10)) : Prop where
  retained : ∀ a,OutsideNode u node a→m a=input a
  child : ∀ i : Fin («cap»+1),m (N.starts+i.val)=
    (childWidth N «cap» (numeric input) (N.starts+i.val):Word (16*u^10))

local notation "seen" m:arg => SiteRead u node cap (J).nodePorts input m
local notation "paidAt" i:arg m:arg => ∀ j : Fin (recordedRoleCount (active i)),
  (issuedRows i m).pairCost j +
    HistoryGatherExecution.tariff W (withParty (cloud i) ((roles i) j).val.val)
      ((issuedRows i m).plan j) ≤ rate i j

set_option maxHeartbeats 1400000 in
/-- Scan the incidence prefix and its physically executed padded suffix in
chronological order. Each occupied row supplies its bound on the exact
compiler-chosen network. Earlier-node reads and old child widths are recovered
at the next slot from the actual compiled writes. -/
theorem recorded_roster (age : 16≤u) (_nodeRoom : node<V₁^2) (capRoom : cap+1≤V₁)
    (available : count≤(J).party.motifs)
    (occupied : ∀ i : Fin count,seen (atSlot i.val) →
      (slot i (atSlot i.val)).Live node encode (atSlot i.val) ∧
      (slot i (atSlot i.val)).ArmSpace node encode (atSlot i.val) u ∧ paidAt i (atSlot i.val))
    (padding : ∀ i : Fin (J).party.motifs,count ≤ i.val→seen (atSlot i.val) →
      let Z:=emptySlot (F:=F) («W»:=W) («p»:=p) (withMotif J i.val)
      Z.Live node encode (atSlot i.val) ∧ Z.ArmSpace node encode (atSlot i.val) u) :
    (∀ j : Fin (J).party.motifs,(st j).Live node encode (atSlot j.val) ∧
      (st j).ArmSpace node encode (atSlot j.val) u) ∧
      (∀ i : Fin count,paidAt i (atSlot i.val)) ∧ seen (atSlot (J).party.motifs) := by
  let banks:=PhysicalBanks.layout u (archive B start height K) f
  have next (j : Fin (J).party.motifs) (scan : seen (atSlot j.val)) :
      (st j).Live node encode (atSlot j.val) ∧ (st j).ArmSpace node encode (atSlot j.val) u := by
    by_cases lt:j.val<count
    · let i : Fin count:=⟨j.val,lt⟩
      have facts:=occupied i scan
      change ((run).slot i.val (atSlot i.val)).Live node encode (atSlot i.val) ∧
        ((run).slot i.val (atSlot i.val)).ArmSpace node encode (atSlot i.val) u
      rw [recordedSite_occupied]
      exact ⟨facts.1,facts.2.1⟩
    · rw [recordedSite_padding (B:=B) (after:=Nat.le_of_not_gt lt)]
      exact padding j (Nat.le_of_not_gt lt) scan
  have visit (k : ℕ) (bound : k≤(J).party.motifs) : seen (atSlot k) := by
    induction k with
    | zero=>
      refine ⟨fun a safe=>starts_outside (archive B start height K) f input age cap capRoom safe,?_⟩
      intro i
      simp only [SiteRun.entry, List.range_zero, List.foldl_nil]
      rw [fillSegment,ite_eq_left ⟨Nat.le_add_right _ _,Nat.add_lt_add_left i.isLt _⟩]
    | succ k ih=>
      let j : Fin (J).party.motifs:=⟨k,by omega⟩
      have prior:=ih (by omega)
      have pair:=next j prior
      have advance : atSlot (k+1)=(st j).endState node encode (atSlot k):=by
        simp only [SiteRun.entry,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]; rfl
      rw [advance]
      exact ⟨fun a safe=>((st j).endState_outsideNode node encode (atSlot k) (banks.withMotif k)
          pair.1 pair.2 a safe).trans (prior.retained a safe),
        fun i=>((st j).child_prefix_end node encode (atSlot k) (banks.withMotif k)
          pair.1 pair.2 i.val (i.isLt.trans_le capRoom)).trans (prior.child i)⟩
  exact ⟨fun j=>next j (visit j.val j.isLt.le),
    fun i=>(occupied i (visit i.val (i.isLt.le.trans available))).2.2,visit _ le_rfl⟩


/-- In addition to inherited cache and child columns, the current party sees
the private prefix initialized for this incidence, for all eight source edges
and the final total. -/
structure ArmRead (u node «cap» : ℕ) (A : HistoryGatherBody.Layout)
    (input start now : Memory (16*u^10)) : Prop extends SiteRead u node «cap» A.nodePorts input now where
  privatePrefix : ∀ j : Fin 9,now (A.privateStarts+j.val)=
    headerImage (privateHeader A (16*u^10)) A.privateStarts 9 start (A.privateStarts+j.val)

/-- Recover retained archive rows and the two selected prefixes even during the
port gather, after the checks and payload have used their workspace banks. -/
theorem ArmRead.gathered {A : HistoryGatherBody.Layout} {u node «cap» : ℕ}
    {initial start now paired scratch : Memory (16*u^10)} (read : ArmRead u node «cap» A initial start now)
    (banks : PhysicalBanks u A) (j : Fin A.party.parties)
    (nr : node<A.party.V^2) (ceiling : (A.party.motifs+2)*(A.party.parties+2)*8*32≤A.party.V)
    (motif : A.party.motif<A.party.motifs) (available : «cap»+1≤A.party.V)
    (narrow : 3+5*A.demandCap+4*A.supplyCap≤A.party.V) (reserve : 9≤volume u)
    (previous : ∀x,OutsideNode u node x→paired x=now x)
    (owns : ∀x,PartyAway u (withParty A j.val).party node x→paired x=now x)
    (frame : DescriptorScan.agreesOutside A.temp (HistoryGatherExecution.portsEnd A) scratch paired) :
    (∀x,base u 18≤x→OutsideNode u node x→scratch x=initial x) ∧
    (∀k:Fin («cap»+1),scratch (A.nodePorts.starts+k.val)=
      (childWidth A.nodePorts «cap» (numeric initial) (A.nodePorts.starts+k.val):Word (16*u^10))) ∧
    (∀k:Fin 9,scratch (A.privateStarts+k.val)=
      headerImage (privateHeader A (16*u^10)) A.privateStarts 9 start (A.privateStarts+k.val)) := by
  have wide : 1+A.demandCap+A.supplyCap≤A.party.V:=by omega
  have mult:=Nat.mul_le_mul_right A.party.V wide
  rw [banks.wordCount] at mult available
  have growth : (volume u)^2≤(volume u)^4:=Nat.pow_le_pow_right (Nat.two_pow_pos _) (by decide)
  have limit:=Diagonal.TickWorkspace.apart (u:=u) (by decide:17<18)
  change base u 17+(volume u)^4≤base u 18 at limit
  have end_ : HistoryGatherExecution.portsEnd A≤base u 18 := by
    change A.temp+(1+A.demandCap+A.supplyCap)*A.party.V≤_
    rw [banks.gather,banks.wordCount]
    rw [pow_two] at growth
    omega
  have held (x : ℕ) (lo : base u 18≤x) (hi : x<base u 18+5*volume u) : scratch x=now x :=
    (frame x (.inr (end_.trans lo))).trans (owns x ((banks.withParty j.val).savedParty nr ceiling motif j.isLt lo hi))
  refine ⟨fun x lo outside=>(frame x (.inr (end_.trans lo))).trans ((previous x outside).trans (read.retained x outside)),?_,?_⟩
  · intro k
    have address:=banks.childStarts
    exact (held _ (by omega) (by have:=k.isLt;omega)).trans (read.child k)
  · intro k
    have address:=banks.privateStarts
    exact (held _ (by omega) (by have:=k.isLt;omega)).trans (read.privatePrefix k)

local notation "bank" i:arg => withMotif J (Fin.val i)

private theorem read_siteInit_outside {F₀ : Type} [Field F₀] [Fintype F₀]
    {w ports : ℕ} {layout₀ : HistoryGatherBody.Layout} (z : SiteSlot F₀ w ports layout₀)
    (m : Memory w) (a : ℕ) (miss : ¬(layout₀.privateStarts ≤ a ∧ a < layout₀.privateStarts + 9)) :
    z.init m a = m a := by
  simp only [SiteSlot.init, HistoryMotifJoin.headerImage, fillSegment, ite_eq_right miss]

set_option maxHeartbeats 1600000 in
/-- The sparse reads required by the selected or dormant arm are available
after every earlier arm, including earlier elected arms in the same motif. -/
theorem SiteRead.at_party {k partyIndex : ℕ} (m : Memory W) (pre : seen m)
    (Z : SiteSlot F W p (withMotif J k)) (age : 16≤u) (few : cap+1≤V₁)
    (held : Z.prefixWords (u:=u) node encode m partyIndex) :
    ArmRead u node cap (withMotif J k) input m (Z.arms.entry node encode (Z.init m) partyIndex) := by
  have big : 128≤V₁:=by
    change 2^7≤2^(u^10)
    exact Nat.pow_le_pow_right (by decide) ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have interval : 10*V₁ ≤ TickWorkspace.stride u:=by
    change 10*V₁≤V₁^4
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ ((by omega : 10≤V₁).trans (Nat.le_self_pow (by decide) _))
  have a14:=apart (u:=u) (by decide : 14<18)
  have a18:=apart (u:=u) (by decide : 18<19)
  have headerStart : (withMotif J k).privateStarts = base u 18+4*V₁ := rfl
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a outside
    have sep:=outside.scratch_range (lo:=base u 18+4*V₁) (hi:=base u 18+4*V₁+9)
      (by omega) (by omega) (.inr (by omega))
    have free : ¬(base u 18+4*V₁≤a ∧ a<base u 18+4*V₁+9):=by omega
    have keep := read_siteInit_outside Z m a (by simpa only [headerStart] using free)
    exact (held a (.inl outside)).trans (keep.trans (pre.retained a outside))
  · intro j
    have jt:=j.isLt.trans_le few
    have span : base u 18≤(J).nodePorts.starts+j.val ∧ (J).nodePorts.starts+j.val<base u 18+5*V₁:=by
      change base u 18≤base u 18+3*V₁+j.val ∧ base u 18+3*V₁+j.val<base u 18+5*V₁;omega
    have free : ¬(base u 18+4*V₁≤(J).nodePorts.starts+j.val ∧ (J).nodePorts.starts+j.val<base u 18+4*V₁+9):=by
      change ¬(base u 18+4*V₁≤base u 18+3*V₁+j.val ∧ _);omega
    have keep := read_siteInit_outside Z m ((J).nodePorts.starts+j.val) (by
      simpa only [headerStart] using free)
    exact (held _ (.inr span)).trans (keep.trans (pre.child j))
  · intro j
    apply held _ (.inr ?_)
    change base u 18≤base u 18+4*V₁+j.val ∧ base u 18+4*V₁+j.val<base u 18+5*V₁
    have:=j.isLt
    omega



open Diagonal.MotifKernel PhysicalPinsExpr PhysicalProcedure HistoryGatherBody
open Diagonal.NavigationDirectory Resident
local notation "arch" => archive B start height K
local notation "dims₀" => dims S (Fintype.card (X).Base) t rem
local notation "en" c:arg => allocate K c (.shrink dims₀)
local notation "fields₀" c:arg field:arg => DescriptorSpan.fields K c dims₀ lay field
local notation "siteNo" => Incidents.siteNumber (X).order v
local notation "owns" i:arg => fun e=>wireOwner supplyGraph.tail supplyGraph.head (partySite P lay (row i)) e=some v
local notation "widths" i:arg => shrinkIssuedWords B.shrink s D rem hD small A branch (row i)
local notation "indices" i:arg => HistoryMaskOrder.order (owns i)
local notation "maps" i:arg j:arg => (withParty (cloud i) ((roles i) j).val.val)
local notation "compiled" => fun (i : Fin count)=>(piece (row i)).compile
local notation "Xexec" => (run).endState node encode first compiled

local notation "inputChart₀" => StageAddress.shrinkInputIso (X).graph (X).chart (shrinkRecordLane s rem) P rfl (X).width
local notation "siteCopies₀" => children v

/-- Read the sum of the actual S13 child-width columns in their S44 list order. -/
theorem recorded_child_prefix {n W₀:ℕ} (N:HistoryNodePorts.Layout) (T:HistoryStageRoot.Input)
    (entry:Memory W₀) (value:Fin n→ℕ)
    (current:numeric entry N.cursor-1=T.id) (nodes:N.nodes=T.nodeBase) (cache:N.cache=T.resultBase)
    (degree:HistoryStageRoot.childCount T (numeric entry)=n)
    (child:∀i,HistoryStageRoot.oldHalf (HistoryStageRoot.atResult (numeric entry)
      (HistoryStageRoot.childPtr T (numeric entry) i.val))=value i) (k «cap»:ℕ) (le:k≤n) :
    childWidth N «cap» (numeric entry) (N.starts+k)=∑ i:Fin k,value (i.castLE le) := by
  have deg:numeric entry (N.nodes+8*(numeric entry N.cursor-1)+4)=n:=by
    rw [nodes,current];exact degree
  rw [childWidth,Nat.add_sub_cancel_left,deg,min_eq_left le]
  have eqn:HistoryNodePorts.sum N (numeric entry) k=HistoryStageRoot.prefix T (numeric entry) k HistoryStageRoot.oldHalf:=by
    unfold HistoryNodePorts.sum HistoryStageRoot.prefix
    rw [current,nodes,cache]
    rfl
  rw [eqn]
  exact HistoryStageRoot.prefix_value (T:=T) (m:=numeric entry) HistoryStageRoot.oldHalf value child k le

set_option maxRecDepth 22000 in
set_option maxHeartbeats 3200000 in
/-- During scratch expansion every old bit lands in the archived half row of the
actual child. The hypotheses describe the original node directory and cache.
No hypothesis asserts the requested bit's value at a later RAM state. -/
theorem recorded_old_source_cells {cur₀:Word W} {m₀ out₀:Memory W} {c:Cursor}
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur₀ m₀ c branch out₀)
    (L:(X).Words Pins) (orderL:(X).OrderedHalves L) (sameLayout:previous=(inputChart₀).pushWord L)
    (sites:(X).ArchiveSites) (T:HistoryStageRoot.Input) (id:T.id=node)
    (nodes:T.nodeBase=base u 44) (cache:T.resultBase=base u 13)
    (degree₀:HistoryStageRoot.childCount T (numeric input)=siteCopies₀)
    (cached:∀k:Fin siteCopies₀,HistoryStageRoot.oldHalf (HistoryStageRoot.atResult (numeric input)
      (HistoryStageRoot.childPtr T (numeric input) k.val))=previous.ports.halfBits (childOrder v k).val)
    (age:16≤u) (nr:node<V₁^2) (cursor:numeric input (base u 18)-1=node)
    (few:siteCopies₀≤cap) (prefixRoom:(J).nodePorts.starts+siteCopies₀<2^W)
    (pinRoom:WordLayout.prior previous ((P).placement lay) children childOrder v<2^W)
    (oldRows:State.HalfRows sites (fun a=>base u 19≤a ∧ a<2^W) (numeric input))
    (directory:∀x,base u 44+(8*sites.id x+6)<2^W ∧
      numeric input (base u 44+(8*sites.id x+6))=sites.layer.incident+(sites.ord x).val*2)
    (childPtr:ℕ) (childTable:numeric input (HistoryStageRoot.node T+3)=childPtr)
    (arr:base u 19≤childPtr ∧ childPtr+siteCopies₀≤2^W)
    (childIds:∀k:Fin siteCopies₀,numeric input (childPtr+k.val)=
      sites.id ((inputChart₀).site.symm ((childOrder v k).val)))
    (i:Fin count) (j:Fin (recordedRoleCount (active i))) (scratch:Memory W)
    (preserves:∀a,base u 18≤a→OutsideNode u node a→scratch a=input a)
    (starts:∀k:Fin (cap+1),scratch ((J).nodePorts.starts+k.val)=
      (childWidth (J).nodePorts cap (numeric input) ((J).nodePorts.starts+k.val):Word W)) :
    let r:=(roles i) j
    let dp:=(Fintype.equivFin (demandGraph.Port r.val)).symm
    ∀ (q:Fin (Fintype.card (demandGraph.Port r.val)))
      (bit:Fin (PhysicalShrink.b P oldWidth₀ (shrinkRecordCode s rem A) hc (row i) ((dp q).val.1))),
      HistoryGatherExecution.DemandCells B.shrink s D rem hD small A branch (maps i j) scratch (row i) r.val q.val
        previous successor v r.property (dp q) bit := by
  subst previous
  let arm:=maps i j
  have cursorBeforeScratch := TickWorkspace.apart (u:=u) (by decide : 18 < 19)
  have upper:=TickWorkspace.apart (u:=u) (by decide:19<44)
  have high (x:ℕ) (lo:base u 19≤x) : scratch x=input x:=
    preserves _ (by omega) (outside_of_region node age nr (.inr (.inl lo)))
  have cursorRead : scratch (base u 18)=input (base u 18):=
    preserves _ le_rfl (outside_of_region node age nr (.inr (.inr (.inl rfl))))
  have current : numeric scratch arm.nodePorts.cursor-1=T.id:=by
    change (scratch (base u 18)).val-1=T.id
    rw [cursorRead,id];exact cursor
  have nroom:=HistoryShrinkEmitter.directory_address_space (u:=u) age
    (Nat.pow_le_pow_right (by decide:0<2) ((by omega:7≤u).trans (Nat.le_self_pow (by decide) _))) nr
  have room : HistoryStageRoot.node T+6<2^W:=by simpa [HistoryStageRoot.node,nodes,id] using
    (show base u 44+8*node+6<2^W by omega)
  have addrHigh (k:ℕ) : base u 19≤HistoryStageRoot.node T+k:=by rw [HistoryStageRoot.node,nodes];omega
  have degree : numeric scratch (HistoryStageRoot.node T+4)=siteCopies₀:=
    (congrArg Fin.val (high _ (addrHigh 4))).trans degree₀
  have head:=HistoryRefreshEmitter.selected_source_header arm T scratch current (by rw [nodes];rfl)
    (Nat.one_lt_two_pow (Nat.ne_of_gt (Nat.mul_pos (by decide) (Nat.pow_pos (by omega : 0 < u))))) (by change base u 18<2^W;omega)
    room (by rw [degree];exact prefixRoom)
  have child : (selected arm scratch).childIDs.val=childPtr:=by
    rw [head.1,high _ (addrHigh 3)];exact childTable
  have savedRows : State.HalfRows sites (fun a=>a<2^W) (numeric scratch):=
    oldRows.transfer (fun x hx=>congrArg Fin.val (high _ hx.1)) (fun _ hx=>hx.2)
  intro selectedRole portOrder q bit
  apply recorded_demand_cells (B:=B) («s»:=s) («D»:=D) (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (H:=H) (site:=v) (O:=order) («slot»:=i)
    («J»:=cloud i) (successor:=successor) (cur:=cur₀) (before:=m₀) (c:=c) (issued:=out₀) (part:=(roles i) j) L orderL sites scratch q bit savedRows
  · exact (congrArg (fun ptr : ℕ => ptr + siteCopies₀) child).le.trans arr.2
  · exact fun x=>(directory x).1
  · change base u 44<2^W;omega
  · exact prefixRoom
  · intro k
    have same := congrArg (fun ptr : ℕ => (scratch (ptr+k.val)).val) child
    have oldCell := congrArg Fin.val (high (childPtr+k.val) (arr.1.trans (Nat.le_add_right ..)))
    exact same.trans (oldCell.trans (childIds k))
  · intro x
    change (scratch (base u 44+(8*sites.id x+6))).val=_
    rw [high _ (by omega)];exact (directory x).2
  · intro k
    let a:Fin (cap+1):=⟨k.val,by have:=k.isLt;omega⟩
    have data:=starts a
    have val:=recorded_child_prefix (J).nodePorts T input
      (fun x=>((inputChart₀).pushWord L).ports.halfBits (childOrder v x).val)
      (cursor.trans id.symm) (by rw [nodes];rfl) (by rw [cache];rfl) degree₀ cached k.val cap k.isLt.le
    change scratch ((J).nodePorts.starts+k.val)=(childWidth (J).nodePorts cap (numeric input) ((J).nodePorts.starts+k.val):Word W) at data
    rw [val] at data
    have le : (∑ a:Fin k.val,((inputChart₀).pushWord L).ports.halfBits (childOrder v (a.castLE k.isLt.le)).val)≤
        WordLayout.prior ((inputChart₀).pushWord L) ((P).placement lay) children childOrder v :=
      Finset.sum_le_sum_of_injOn (Fin.castLE k.isLt.le) (fun _ _ _ _ h => (Fin.castLEEmb k.isLt.le).injective h)
        (Finset.subset_univ _) (fun _ _=>le_rfl) (fun _ _ _=>Nat.zero_le _)
    exact (congrArg Fin.val data).trans (Fin.val_cast_of_lt (le.trans_lt pinRoom))

local notation "freshDegree₀" => Graph.liveDegree S+pad
local notation "halfHead₀" c:arg => fields₀ c 38+2*siteNo
local notation "halfTable₀" c:arg => fields₀ c 40+siteNo*(8*D)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 4200000 in
/-- Resolve the fresh or private source directly against the shrink's real
published half rows. The raw half order here is the order used by the typed
shrink piece, before the final degree equality casts the numbered graph. -/
theorem recorded_fresh_source_cells (cur ctr:Word W) (before issued final:Memory W) (c:Cursor) (hdr:ℕ)
    (H:ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved:SavedFrame cur ctr hdr (en c).next.header (en c).next.heap issued final)
    (range:hdr≤c.heap ∧ base u 19≤c.heap)
    (guard:∀a,c.heap≤a→a<(en c).next.heap→a≠cur.val ∧ a≠ctr.val)
    (original:∀a,c.heap≤a→a<(en c).next.heap→input a=final a)
    (T:HistoryStageRoot.Input) (id:T.id=node) (nodes:T.nodeBase=base u 44) (cache:T.resultBase=base u 13)
    (countNew:successor.count v=2*freshDegree₀)
    (orderNew:∀k,successor.order v k=HalfOrder.order Gnew v (k.cast countNew))
    (degree₀:HistoryStageRoot.childCount T (numeric input)=siteCopies₀)
    (cached:∀k:Fin siteCopies₀,HistoryStageRoot.oldHalf (HistoryStageRoot.atResult (numeric input)
      (HistoryStageRoot.childPtr T (numeric input) k.val))=previous.ports.halfBits (childOrder v k).val)
    (fresh:HistoryStageRoot.halfWidth T (numeric input)=successor.ports.halfBits v)
    (headAt:numeric input (HistoryStageRoot.node T+6)=halfHead₀ c)
    (age:16≤u) (nr:node<V₁^2) (current:numeric input (base u 18)-1=node)
    (few:siteCopies₀≤cap) (prefixRoom:(J).nodePorts.starts+siteCopies₀<2^W)
    (dpFit:2*D<2^W) (laneFit:2^rem<2^W) (pinRoom:p<2^W) (privRoom:(J).privateStarts+9<2^W)
    (i:Fin count) (j:Fin (recordedRoleCount (active i))) (startM:Memory W)
    (privateRows:PrivateSite (geo:=S) (cloud i) startM (owns i) (widths i))
    (widthRoom : Finset.univ.sum (fun e : Fin 8 => (widths i) e) < 2^W)
    (scratch:Memory W) (preserves:∀a,base u 18≤a→OutsideNode u node a→scratch a=input a)
    (starts:∀k:Fin (cap+1),scratch ((J).nodePorts.starts+k.val)=
      (childWidth (J).nodePorts cap (numeric input) ((J).nodePorts.starts+k.val):Word W))
    (savedPrefix:∀k:Fin 9,scratch ((J).privateStarts+k.val)=
      headerImage (privateHeader (cloud i) W) (J).privateStarts 9 startM ((J).privateStarts+k.val)) :
    let role:=(roles i) j
    let sp:=(Fintype.equivFin (supplyGraph.Port role.val)).symm
    ∀ (q:Fin (Fintype.card (supplyGraph.Port role.val))) (bit:Fin ((widths i) ((sp q).val.1))),
      HistoryGatherExecution.SupplyCells B.shrink s D rem hD small A branch H (maps i j) scratch (row i)
        role.val q.val previous successor v (sp q) bit := by
  let arm:=maps i j
  let n:=siteCopies₀
  let ht:=halfHead₀ c
  let tab:=halfTable₀ c
  let oldSize:=WordLayout.prior previous ((P).placement lay) children childOrder v
  have deg:freshDegree₀=D:=PhysicalShrink.degree_eq hc (Nat.two_pow_pos _) hD
  have rawHalfRows := ShrinkOutput.selected_raw_halves
    (T := B.shrink) («s» := s) («D» := D) (rem := rem) (hD := hD) (small := small) (A := A)
    (cur := cur) (m := before) (c := c) (branch := branch) H dpFit laneFit v
  obtain ⟨hLow,hEnd,tLow,tEnd,cnt,ptr,words⟩:=rawHalfRows
  have upper:(en c).next.heap<2^W:=H.cursor.controls.trans_lt cur.isLt
  have cursorBeforeScratch := TickWorkspace.apart (u:=u) (by decide : 18 < 19)
  have gap:=TickWorkspace.apart (u:=u) (by decide:19<44)
  have high (a:ℕ) (lo:base u 19≤a) : scratch a=input a:=
    preserves _ (by omega) (outside_of_region node age nr (.inr (.inl lo)))
  have retained (a:ℕ) (lo:c.heap≤a) (hi:a<(en c).next.heap) : input a=issued a:=by
    obtain ⟨h,g⟩:=guard _ lo hi
    exact (original a lo hi).trans (saved _ h g (.inr (range.1.trans lo)) hi)
  have hold (a:ℕ) (lo:c.heap≤a) (hi:a<(en c).next.heap) : scratch a=issued a:=
    (high a (range.2.trans lo)).trans (retained a lo hi)
  have raw (a:ℕ) (lo:base u 19≤a) : numeric scratch a=numeric input a:=congrArg Fin.val (high a lo)
  have nd (k:ℕ):base u 19≤HistoryStageRoot.node T+k:=by rw [HistoryStageRoot.node,nodes];omega
  have headInput:numeric input (HistoryStageRoot.node T+6)=ht:=headAt
  have nc:numeric input ht=2*freshDegree₀:=by
    rw [numeric,retained _ hLow (by omega),cnt]
    exact Fin.val_cast_of_lt (deg.symm ▸ dpFit)
  have np:numeric input (ht+1)=tab:=by
    rw [numeric,retained _ (by omega) hEnd,ptr]
    exact Fin.val_cast_of_lt (by omega)
  have halfCountPositive:0<2*freshDegree₀:=by rw [deg];omega
  have lastRoom : tab+4*(2*freshDegree₀-1)+3<2^W:=by omega
  have transferred:HistoryStageRoot.halfWidth T (numeric scratch)=HistoryStageRoot.halfWidth T (numeric input):=by
    unfold HistoryStageRoot.halfWidth
    simp only [raw _ (nd 6),headInput,raw ht (range.2.trans hLow),raw (ht+1) (by omega),nc,np]
    rw [raw _ (by omega),raw _ (by omega)]
  have hr:HistoryStageRoot.node T+6<2^W:=by
    have big:128≤V₁:=Nat.pow_le_pow_right (by decide:0<2) ((by omega:7≤u).trans (Nat.le_self_pow (by decide) _))
    have full:=HistoryShrinkEmitter.directory_address_space (u:=u) age big nr
    rw [HistoryStageRoot.node,nodes,id];omega
  have cr:base u 18<2^W:=by rw [HistoryStageRoot.node,nodes] at hr;omega
  have curNow:numeric scratch arm.nodePorts.cursor-1=T.id:=by
    change (scratch (base u 18)).val-1=T.id
    rw [preserves _ le_rfl (outside_of_region node age nr (.inr (.inr (.inl rfl)))),id];exact current
  have cntNow:numeric scratch (HistoryStageRoot.node T+4)=n:=(raw _ (nd 4)).trans degree₀
  have htNow:numeric scratch (HistoryStageRoot.node T+6)=ht:=(raw _ (nd 6)).trans headInput
  have nb:arm.nodePorts.nodes=T.nodeBase:=by rw [nodes];rfl
  have fits : 1 < 2^W := Nat.one_lt_two_pow (Nat.ne_of_gt (Nat.mul_pos (by decide) (Nat.pow_pos (by omega : 0 < u))))
  have head:=HistoryRefreshEmitter.selected_source_header arm T scratch curNow nb fits cr hr (by rw [cntNow];exact prefixRoom)
  have oldValue:=recorded_child_prefix (J).nodePorts T input (fun x=>previous.ports.halfBits (childOrder v x).val)
    (current.trans id.symm) (by rw [nodes];rfl) (by rw [cache];rfl) degree₀ cached n cap le_rfl
  have pre : scratch ((J).nodePorts.starts+n)=(oldSize:Word W):=by
    simpa only [oldSize,WordLayout.prior,Fin.castLE_refl,oldValue] using starts ⟨n,by omega⟩
  have prefixRead : scratch (arm.nodePorts.starts+n)=(oldSize:Word W) := pre
  have oldWord : (selected arm scratch).oldBits=(oldSize:Word W) :=
    head.2.2.trans ((congrArg (fun k : ℕ => scratch (arm.nodePorts.starts+k)) cntNow).trans prefixRead)
  have oldBits : (selected arm scratch).oldBits.val=oldSize :=
    (congrArg Fin.val oldWord).trans (Fin.val_cast_of_lt (by
      change oldSize+successor.ports.halfBits v<2^W at pinRoom
      omega))
  have total:=HistoryRefreshEmitter.root_ports arm T scratch n oldSize (successor.ports.halfBits v)
    curNow nb fits cr hr (by rw [htNow];omega) (fun _=>by
      change numeric scratch (numeric scratch (HistoryStageRoot.node T+6)+1)+
        4*(numeric scratch (numeric scratch (HistoryStageRoot.node T+6))-1)+3<2^W
      rw [htNow,raw _ (by omega),raw _ (by omega),np,nc];exact lastRoom)
    cntNow prefixRoom pre (transferred.trans fresh)
  have halfPtr:(selected arm scratch).newHalves.val=ht:=(congrArg Fin.val head.2.1).trans htNow
  have headerRoom : (selected arm scratch).newHalves.val+1<2^W :=
    lt_of_eq_of_lt (congrArg (fun a : ℕ => a+1) halfPtr) (lt_trans hEnd upper)
  have tableRead : (scratch ((selected arm scratch).newHalves.val+1)).val=tab :=
    (congrArg (fun a : ℕ => (scratch (a+1)).val) halfPtr).trans
      ((raw (ht+1) ((range.2.trans hLow).trans (Nat.le_succ ht))).trans np)
  have bound:successor.ports.halfBits v<2^W:=by change oldSize+successor.ports.halfBits v<2^W at pinRoom;omega
  intro selectedRole portOrder q bit
  apply recorded_supply_cells (B:=B) («s»:=s) («D»:=D) (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (H:=H) (site:=v) (O:=order) («slot»:=i)
    («J»:=cloud i) (previous:=previous) (successor:=successor) (cur:=cur) (before:=before) (c:=c) (issued:=issued) (part:=(roles i) j) scratch startM q bit oldBits
    ((congrArg Fin.val total).trans (Fin.val_cast_of_lt pinRoom)) countNew orderNew privateRows privRoom
    (fun e=>savedPrefix (e.castLE (by decide))) widthRoom headerRoom tab tableRead (by omega)
  intro k
  have inRange : tab+4*k.val+3<(en c).next.heap:=by have:=k.isLt;omega
  rw [hold _ (by omega) inRange,words k]
  exact Fin.val_cast_of_lt ((SupplySend.successor_prefix_le Gnew v successor countNew orderNew k).trans_lt bound)

/-- All gather decoder reads bypass S17. The final two columns are addressed
by the actual mounted page, including its entire padded supply field. -/
theorem recorded_port_window {u:ℕ} {«J»:HistoryGatherBody.Layout} {m:Memory (16*u^10)}
    {x:Native.ShrinkStage.Dimensions} {ptr:Native.ShrinkStage.Pointers}
    (node kernel incident page len:ℕ)
    (cursor:«J».nodePorts.cursor=base u 18) (nodes:«J».nodePorts.nodes=base u 44)
    (room:base u 44+8*node+8<2^(16*u^10)) (current:numeric m «J».nodePorts.cursor-1=node)
    (cursorFit:base u 18<2^(16*u^10)) (one:1<2^(16*u^10))
    (pk:(selected «J» m).kernel=(kernel:Word (16*u^10))) (pi:(selected «J» m).incident=(incident:Word (16*u^10)))
    (pp:(selected «J» m).portPage=(page:Word (16*u^10))) (kf:kernel+5<2^(16*u^10))
    (rf:incident+6<2^(16*u^10)) (pf:page+len≤2^(16*u^10))
    (dlen:3+2*«J».demandCap+«J».supplyCap≤len)
    (kh:base u 18≤kernel) (ih:base u 18≤ incident) (ph:base u 18≤page)
    (safe:∀a,Resident.GeometryRead x ptr a→base u 18≤a)
    (stop:HistoryGatherExecution.portsEnd «J»≤base u 18) : PortFootprint «J» m x ptr := by
  have fit:(HistoryNodePorts.id «J».nodePorts).Fits (16*u^10) (fun _=>0) (numeric m) (fun _=>0):=
    ⟨⟨trivial,cursor.symm ▸ cursorFit⟩,trivial,(m «J».nodePorts.cursor).isLt,one⟩
  have eval:=Formula.value_eq_natural (HistoryNodePorts.id «J».nodePorts) (fun _=>0) (numeric m) (fun _=>0) fit
  rw [word_numeric] at eval
  have ix:(HistoryNodePorts.id «J».nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word (16*u^10)):=by
    exact eval.trans (congrArg (fun n : ℕ => (n : Word (16*u^10))) current)
  have loc:nodeWord «J» m=((base u 44+8*node:ℕ):Word (16*u^10)):=by
    change («J».nodePorts.nodes:Word (16*u^10))+8*((HistoryNodePorts.id «J».nodePorts).value (fun _=>0) m (fun _=>0))=_
    simp only [nodes,ix,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have plus (a k:ℕ) (h:a+k<2^(16*u^10)) :
      ((a:Word (16*u^10))+(k:Word (16*u^10))).val=a+k:=by rw [←Nat.cast_add,Fin.val_cast_of_lt h]
  have cursorBeforeNodes:=TickWorkspace.apart (u:=u) (by decide:18<44)
  constructor
  · right;rw [cursor,Fin.val_cast_of_lt cursorFit];exact stop
  · right;rw [loc,show (5:Word (16*u^10))=((5:ℕ):Word (16*u^10)) by rfl,plus _ _ (by omega)];omega
  · right;rw [pk,show (4:Word (16*u^10))=((4:ℕ):Word (16*u^10)) by rfl,plus _ _ (by omega)];omega
  · right;rw [pi,show (2:Word (16*u^10))=((2:ℕ):Word (16*u^10)) by rfl,plus _ _ (by omega)];omega
  · right;rw [pi,Fin.val_cast_of_lt (by omega)];omega
  · right;rw [pk,Fin.val_cast_of_lt (by omega)];omega
  · exact fun a h=>Or.inr (stop.trans (safe a h))
  · intro side k bound
    right
    let index:=if side then HistoryPortCatalogue.supplyBase «J».demandCap+k else HistoryPortCatalogue.demandBase+2*k
    have off:index<len:=by
      cases side <;> simp [index,HistoryPortCatalogue.supplyBase,HistoryPortCatalogue.demandBase,
        HistoryGatherExecution.cap] at * <;> omega
    change HistoryGatherExecution.portsEnd «J»≤((selected «J» m).portPage+(index:Word (16*u^10))).val
    rw [pp,plus _ _ (by omega)];omega

open private recordedRoleAt from OAI.ThreeFlat.RAM.HistoryShrinkBatchRecords in
open private selectedIncidentWord from OAI.ThreeFlat.RAM.HistoryMotifTariffShrinkParty in
set_option maxRecDepth 26000 in
set_option maxHeartbeats 5500000 in
/-- The actually reached positive arm of the selected roster. The two native
boots and the row choice are recovered from the retained archive. The final
function consumes the geometrical source reads and the address bounds for the
gather that follows those boots. -/
abbrev recorded_positive_arm (cur ctr : Word W) (before issued final : Memory W)
    (c : Cursor) (hdr : ℕ)
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved : SavedFrame cur ctr hdr (en c).next.header (en c).next.heap issued final)
    (oldCap : ShrinkOldCaps s rem W) (baseRoom : Fintype.card (X).Base≤2^W) (wide : 8≤W)
    (icRoom : Incidents.capacity S<2^W) (offset : 0<c.width)
    (guard : ∀a,hdr≤a→a<(en c).next.heap→a≠cur.val ∧ a≠ctr.val)
    (oldArchive : ∀a,hdr≤a→a<(en c).next.heap→input a=final a)
    (kmin : hdr≤fields₀ c 34) (rmin : hdr≤fields₀ c 36) (area : base u 19≤hdr)
    (cursor : numeric input (base u 18)-1=node)
    (original : input (base u 44+8*node+5)=((fields₀ c 34+5*siteNo:ℕ):Word W))
    (caps:ShrinkNativeCaps B.shrink s D rem W A)
    (oldBounds:NavigationPass.OldArrayBounds hdr c A) (headHigh:base u 19≤c.header)
    (headerRead:∀a,c.header≤a→a<c.header+34→input a=issued a)
    (age : 16≤u) (nr : node<V₁^2) (available : count≤(f).motifs)
    (budget : ((f).motifs+2)*((f).parties+2)*8*32≤V₁)
    (headSize:3+5*(f).demands+4*(f).supplies≤V₁) (childRoom:cap+1≤V₁)
    (lib : Mounted B height W start input) (whole : archiveWindow u start (libraryWords B height))
    (romHigh : base u 19 ≤ start) (Kpos : 0<K) (Kfit : K<2^W)
    (dense : ∀ (idx:Fin (shrinkBinaryFamily B.shrink s D rem hD small A).motifs)
      (a:(shrinkBinaryFamily B.shrink s D rem hD small A).alphabet idx),
      let addr:=c.dense+idx.val*K+(Fintype.equivFin _ a).val
      addr≠c.header+27 ∧ hdr≤addr ∧ addr<(en c).next.heap)
    (i : Fin count) (j : Fin (recordedRoleCount (active i))) (startM now : Memory W)
    (reads : ArmRead u node cap (cloud i) input startM now)
    (priorWords:(X).Words Pins) (ordered:(X).OrderedHalves priorWords) (layoutEq:previous=(inputChart₀).pushWord priorWords)
    (priorSites:(X).ArchiveSites) (T₀:HistoryStageRoot.Input) (nodeId:T₀.id=node)
    (nodeBase:T₀.nodeBase=base u 44) (cacheBase:T₀.resultBase=base u 13)
    (countNew:successor.count v=2*freshDegree₀)
    (orderNew:∀k,successor.order v k=HalfOrder.order Gnew v (k.cast countNew))
    (degree₀:HistoryStageRoot.childCount T₀ (numeric input)=siteCopies₀)
    (cached:∀k:Fin siteCopies₀,HistoryStageRoot.oldHalf (HistoryStageRoot.atResult (numeric input)
      (HistoryStageRoot.childPtr T₀ (numeric input) k.val))=previous.ports.halfBits (childOrder v k).val)
    (newBits:HistoryStageRoot.halfWidth T₀ (numeric input)=successor.ports.halfBits v)
    (headAt:numeric input (HistoryStageRoot.node T₀+6)=halfHead₀ c)
    (heapHigh:hdr≤c.heap) (childCap:siteCopies₀≤cap) (prefixRoom:(J).nodePorts.starts+siteCopies₀<2^W)
    (pinRoom:p<2^W) (privRoom:(J).privateStarts+9<2^W)
    (oldRows:State.HalfRows priorSites (fun a=>base u 19≤a ∧ a<2^W) (numeric input))
    (directory:∀z,base u 44+(8*priorSites.id z+6)<2^W ∧
      numeric input (base u 44+(8*priorSites.id z+6))=priorSites.layer.incident+(priorSites.ord z).val*2)
    (childPtr:ℕ) (childTable:numeric input (HistoryStageRoot.node T₀+3)=childPtr)
    (arr:base u 19≤childPtr ∧ childPtr+siteCopies₀≤2^W)
    (childIds:∀k:Fin siteCopies₀,numeric input (childPtr+k.val)=
      priorSites.id ((inputChart₀).site.symm ((childOrder v k).val)))
    (degreeFit:2*D<2^W) (privateRows:PrivateSite (geo:=S) (cloud i) startM (owns i) (widths i))
    (widthRoom:(∑e:Fin 8,(widths i) e)<2^W)
    (siteSize : 4*(siteTree).resources≤V₁)
    (heightRoom : W≤height) (price:ℕ) (copyBound:many (row i)≤price)
    (margin:gridPageRate (arity B) (shrinkGrid B level)*((price+1)*(W+1)^3)≤V₁)
    (countsWin : archiveWindow u (c.dense+(shrinkRecordOrder s rem A (row i)).val*K)
      ((party i j).kind (arity B)).letters)
    (aboveCounts : base u 19≤c.dense)
    (tableTags : Fintype.card ((Fin 3→Bool)→F)≤2^W) :=
  have page:=selected_shrink_page_caps (u:=u) B s D rem hD small A branch v order i level ((roles i) j) price copyBound margin
  have hp:=page.1.trans heightRoom
  have kindSmall:=page.2.1
  have width:=page.2.2.width
  have work:=page.2.2.work
  have rowSpace:=page.2.2.pairRows
  have pinSpace:=page.2.2.pairPins
  have countSpace:=page.2.2.commands
  have hiddenSpace:=page.2.2.pairBits
  let pref := (List.ofFn (shrinkGrid B)).take level.val
  let rest := (List.ofFn (shrinkGrid B)).drop (level.val+1)++[refreshGrid B]
  have stage : grids B=pref++shrinkGrid B level::rest := by
    let xs:=List.ofFn (shrinkGrid B)
    have hi : level.val<xs.length:=by simp [xs]
    have cut:=List.take_append_drop level.val xs
    rw [List.drop_eq_getElem_cons hi,show xs[level.val]=shrinkGrid B level by simp [xs]] at cut
    exact (congrArg (fun a=>a++[refreshGrid B]) cut.symm).trans (by rw [List.append_assoc];rfl)
  let role:Fin (f).parties:=((roles i) j).val
  have high (a:ℕ) (ha:base u 19≤a) : now a=input a :=
    reads.retained a (outside_of_region node age nr (.inr (.inl ha)))
  have current:numeric now (base u 18)-1=node:=by
    rw [numeric,reads.retained _ (outside_of_region node age nr (.inr (.inr (.inl rfl))))];exact cursor
  have numericHead:=recorded_occupied_header B s D rem hD small A u arch f node cur ctr before issued final now
    c branch hdr H saved v order i.val role oldCap baseRoom wide icRoom offset guard
    (fun a lo hi=>(high a (area.trans lo)).trans (oldArchive a lo hi)) kmin rmin area current
    (by rw [high _ (by have:=TickWorkspace.apart (u:=u) (by decide:19<44);omega)];exact original)
    age nr i.isLt
  let kern:=fields₀ c 34+5*siteNo
  let line:=fields₀ c 36+6*(Incidents.capacity S*siteNo+i.val)
  have ⟨kr,ir,live,ptr,kptr,kw,iw,nw,locK,locI⟩:=numericHead
  have kguard (a:Fin 5) : kern+a.val≠cur.val ∧ kern+a.val≠ctr.val ∧ hdr≤kern+a.val:=
    ⟨(guard _ (locK a).1 (locK a).2).1,(guard _ (locK a).1 (locK a).2).2,(locK a).1⟩
  have joints (a:Fin 6) : line+a.val≠cur.val ∧ line+a.val≠ctr.val ∧ hdr≤line+a.val:=
    ⟨(guard _ (locI a).1 (locI a).2).1,(guard _ (locI a).1 (locI a).2).2,(locI a).1⟩
  have rom : Mounted B height W start now := ⟨fun k=>(high _ (by omega)).trans (lib.words k)⟩
  have availableAt : i.val<(f).motifs:=i.isLt.trans_le available
  have pairPtr := ptr.trans (selectedIncidentWord (w:=W) (fields₀ c 36)
    (Incidents.capacity S) siteNo i.val).symm
  let selectedPair:=selected_shrink_pair B s D rem hD small A cur ctr before issued final now c branch hdr H saved v order i
    level stage ((roles i) j) oldCap baseRoom icRoom offset node age nr hp rom whole romHigh current
    availableAt budget kr ir live pairPtr joints (fun a=>(high _ (area.trans (locI a).1)).trans (oldArchive _ (locI a).1 (locI a).2))
    (fun idx a=>by
      obtain ⟨une,lo,hi⟩:=dense idx a
      exact ⟨une,(guard _ lo hi).1,(guard _ lo hi).2,lo,hi,(high _ (area.trans lo)).trans (oldArchive _ lo hi)⟩)
    nw kw iw countsWin ⟨(area.trans kmin).trans (Nat.le_add_right _ _),
      (area.trans rmin).trans (Nat.le_add_right _ _),aboveCounts.trans (Nat.le_add_right _ _)⟩
    width work kindSmall tableTags
  let h:=selectedPair rowSpace pinSpace countSpace hiddenSpace
  let cRead:=Classical.choose h
  let pRead:=Classical.choose (Classical.choose_spec h)
  let facts:=Classical.choose_spec (Classical.choose_spec h)
  let postHigh :=fun a (ha:base u 19≤a)=> (facts.2.1 a (outside_of_region node age nr (.inr (.inl ha)))).trans (high a ha)
  have retainedHeader (m:Memory W) (retain:∀a,OutsideNode u node a→m a=now a) :
      (selected (maps i j) m).kernel=(kern:Word W) ∧ (selected (maps i j) m).incident=(line:Word W) ∧
      numeric m (base u 18)-1=node := by
    have curr:numeric m (base u 18)-1=node:=by
      rw [numeric,retain _ (outside_of_region node age nr (.inr (.inr (.inl rfl))))];exact current
    have field (a:ℕ) (ha:base u 19≤a) : m a=input a:=
      (retain _ (outside_of_region node age nr (.inr (.inl ha)))).trans (high a ha)
    have hr:=recorded_occupied_header B s D rem hD small A u arch f node cur ctr before issued final m
      c branch hdr H saved v order i.val role oldCap baseRoom wide icRoom offset guard
      (fun a lo hi=>(field a (area.trans lo)).trans (oldArchive a lo hi)) kmin rmin area curr
      (by rw [field _ (by have:=TickWorkspace.apart (u:=u) (by decide:19<44);omega)];exact original)
      age nr i.isLt
    exact ⟨hr.2.2.2.2.1,hr.2.2.2.1,curr⟩
  have retainedKernel (m:Memory W) (retain:∀a,OutsideNode u node a→m a=now a) :=
    (retainedHeader m retain).1
  have postIncident:=(retainedHeader _ facts.2.1).2.1
  have postCurrent:=(retainedHeader _ facts.2.1).2.2
  have bigHeap:c.heap≤(en c).next.heap:=by rw [heap_step];omega
  have geomFloor : ∀a,GeometryRead dims₀ (pointers K c dims₀) a→base u 18≤a := by
    have low:base u 18≤base u 19:=(Nat.le_add_right _ _).trans (TickWorkspace.apart (u:=u) (by decide:18<19))
    exact GeometryRead.in_intervals H.cursor _ (fun _ h _=>low.trans (headHigh.trans h))
      (fun _ h _=>low.trans (area.trans (oldBounds.graphLow.trans h)))
      (fun _ h _=>low.trans (area.trans (oldBounds.widthLow.trans h)))
      (fun _ h _=>low.trans (area.trans (heapHigh.trans h)))
  have resumeArchive (a:ℕ) (lo:hdr≤a) (hi:a<(en c).next.heap) : _ :=
    (postHigh a (area.trans lo)).trans ((oldArchive a lo hi).trans
      (saved a (guard a lo hi).1 (guard a lo hi).2 (.inr lo) hi))
  have geometry:=GeometryFrame.of_intervals H.cursor
    (fun a lo hi=>(postHigh a (headHigh.trans lo)).trans (headerRead a lo hi))
    (fun a lo hi=>resumeArchive a (oldBounds.graphLow.trans lo) (hi.trans_le (H.cursor.graph.trans bigHeap)))
    (fun a lo hi=>resumeArchive a (oldBounds.widthLow.trans lo) (hi.trans_le (H.cursor.widths.trans bigHeap)))
    (fun a lo hi=>resumeArchive a (heapHigh.trans lo) hi)
  have demandKeep {m : Memory W}
      (keep : ∀ a, hdr ≤ a → a < (en c).next.heap → m a = issued a) (e : Fin 2) :
      let addr := (pointers K c dims₀).demands + (shrinkRecordOrder s rem A (row i)).val * 2 + e.val
      m addr = issued addr := by
    let x:=dims₀
    let ptr:=pointers K c x
    let ordinal:=(shrinkRecordOrder s rem A (row i)).val
    have ord:ordinal<x.motifs := (shrinkRecordOrder s rem A (row i)).isLt
    obtain ⟨b₀,b₁,b₂,b₃,b₄,b₅,b₆,b₇,b₈,b₉⟩:=H.cursor.allocated
    have next {start stop n : ℕ} (span : stop = start+n) : start ≤ stop :=
      (Nat.le_add_right _ _).trans_eq span.symm
    have low : hdr ≤ ptr.demands := (heapHigh.trans_eq b₀.symm).trans ((next b₁).trans (next b₂))
    have high : ptr.split ≤ ptr.costs := (next b₄).trans <| (next b₅).trans <|
      (next b₆).trans <| (next b₇).trans <| (next b₈).trans (next b₉)
    have finish:ptr.costs≤(en c).next.heap:=by
      change ptr.costs≤extraEnd x (ptr.costs+2*(x.motifs+1));rw [extra_extent];omega
    have indexFits : ordinal*2+e.val < 2*x.motifs := by
      have inside := e.isLt
      omega
    apply keep (ptr.demands+ordinal*2+e.val)
    · exact (low.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
    · calc
        ptr.demands+ordinal*2+e.val = ptr.demands+(ordinal*2+e.val) := Nat.add_assoc ..
        _ < ptr.demands+2*x.motifs := Nat.add_lt_add_left indexFits _
        _ = ptr.split := b₃.symm
        _ ≤ (en c).next.heap := high.trans finish
  let extraCaps:=caps.output
  let top:=shrinkMotifWidthFactor B.shrink (2*d+1) d*(1+A.maxWidth)
  have topWord:top<2^W:=caps.issued
  have issuedSize:=shrink_issued_room B.shrink s D rem hD small A branch
  let demandCap := widthMultiplicity (2*d+1) d*A.maxWidth
  have demandFits : demandCap<2^W :=
    (Nat.le_mul_of_pos_left demandCap (by decide : 0<2)).trans_lt
      ((Nat.le_add_left (2*demandCap) 1).trans_lt
        ((Nat.le_add_right (1+2*demandCap) (shrinkBaseBound B.shrink)).trans_lt caps.demand))
  have multiplierPos : 0<widthMultiplicity (2*d+1) d := Nat.add_pos_left (by decide : 0<1) _
  have oldWord : A.maxWidth<2^W := (Nat.le_mul_of_pos_left A.maxWidth multiplierPos).trans_lt demandFits
  have thickWord : thickWidth P oldWidth₀ ((P).bundle (row i))<2^W := by
    calc
      _ ≤ ∑ _a : ThickAt P ((P).bundle (row i)),A.maxWidth := Finset.sum_le_sum (fun e _=>prior_width_le s rem A e.val)
      _ = 2^((2*d+1)-2)*d*A.maxWidth := by
        simp only [Finset.sum_const,Finset.card_univ,card_thickAt,nsmul_eq_mul,Nat.cast_id]
      _ ≤ demandCap := Nat.mul_le_mul_right A.maxWidth (Nat.le_add_left _ 1)
      _ < 2^W := demandFits

  let upper : V₁<2^W:=by
    have positiveVolume : 0<volume u := Nat.pow_pos (by decide : 0<(2:ℕ))
    have h:=TickWorkspace.word_space (u:=u) (i:=0) (by omega)
      (show 0<(volume u)^4 from Nat.pow_pos positiveVolume)
    change base u 0+(volume u)^4<2^W at h
    exact lt_of_le_of_lt (Nat.le_self_pow (by decide:4≠0) _) (by omega)
  have pageRate : gridPageRate (arity B) (shrinkGrid B level)<2^W :=
    ((Nat.le_mul_of_pos_right _ (by positivity : 0<(price+1)*(W+1)^3)).trans margin).trans_lt upper
  have permanent:=selected_shrink_page_rom (u:=u) B s D rem hD small A branch v order i level stage
    ((roles i) j) whole pageRate
  let emit:=emit_recorded_party (B:=B) («s»:=s) («D»:=D) (rem:=rem) (hD:=hD) (small:=small) (A:=A)
    (cur:=cur) (ctr:=ctr) (before:=before) (issued:=issued) (final:=final) (c:=c) (branch:=branch) (hdr:=hdr)
    (H:=H) (saved:=saved) (site:=v) (O:=order) («slot»:=i) («J»:=cloud i)
    (oldCaps:=oldCap) (baseFit:=baseRoom) (wide:=wide) (capFits:=icRoom) (offset:=offset)
    (apart:=joints) (level:=level) (stage:=stage) (previous:=previous) (successor:=successor)
    (part:=(roles i) j) now node hp rfl rfl rfl rfl rfl rfl rfl rfl Kpos Kfit permanent.1 permanent.2.1.le
    (fun a=>(kindSmall a).trans_lt upper) permanent.2.2 extraCaps top issuedSize topWord oldWord thickWord
    cRead pRead facts.1
  let sourceRead (scratch:Memory W):=reads.gathered (scratch:=scratch) ((PhysicalBanks.layout u arch f).withMotif i.val)
    ((roles i) j).val nr budget availableAt childRoom headSize
    ((by decide:9≤16).trans (Nat.pow_le_pow_right (by decide:0<2) ((by omega:4≤u).trans (Nat.le_self_pow (by decide) _))))
    facts.2.1 facts.2.2
  have stop:HistoryGatherExecution.portsEnd (maps i j)≤base u 18:=by
    change base u 17+(1+(f).demands+(f).supplies)*V₁≤base u 18
    have mult:=Nat.mul_le_mul_right V₁ (show 1+(f).demands+(f).supplies≤V₁ by omega)
    have growth:V₁^2≤V₁^4:=Nat.pow_le_pow_right (Nat.two_pow_pos _) (by decide)
    have limit:=TickWorkspace.apart (u:=u) (by decide:17<18)
    change base u 17+V₁^4≤base u 18 at limit
    rw [pow_two] at growth;omega
  have ageFour : 4 ≤ u := (by decide : 4 ≤ 16).trans age
  have exponentFour : 4 ≤ u^10 := ageFour.trans (Nat.le_self_pow (by decide : 10≠0) u)
  have volumeSixteen : 16 ≤ volume u := by
    change 2^4 ≤ 2^(u^10)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) exponentFour
  have room18 : base u 18 + (volume u)^4 < 2^W :=
    TickWorkspace.word_space ((by decide : 1 ≤ 16).trans age)
      (show 18 < (volume u)^4 from
        (by decide : 18 < (16:ℕ)^4).trans_le (Nat.pow_le_pow_left volumeSixteen 4))
  have pageHeaderFits : HistoryPortCatalogue.headerBase (maps i j).demandCap (maps i j).supplyCap ≤
      (shrinkGrid B level).stride :=
    Nat.le_add_right (3+2*(shrinkGrid B level).demand+(shrinkGrid B level).supply)
      (2*(shrinkGrid B level).digits)
  let footprint:=fun pp=>recorded_port_window (x:=dims₀) (ptr:=pointers K c dims₀)
    node kern line _ (shrinkGrid B level).stride rfl rfl nw.1
    postCurrent (by omega) (by exact Nat.one_lt_two_pow (by omega)) (retainedKernel _ facts.2.1)
    postIncident pp kw.1 iw.1 permanent.2.1.le
    pageHeaderFits
    (by have h:=locK 0;have q:=TickWorkspace.apart (u:=u) (by decide:18<19);omega)
    (by have h:=locI 0;have q:=TickWorkspace.apart (u:=u) (by decide:18<19);omega)
    (by dsimp [shrinkFamily,Grid.family,Mounted.base,gridStart];have q:=TickWorkspace.apart (u:=u) (by decide:18<19);omega)
    geomFloor stop
  have kernelWord : (kern : Word W) = (fields₀ c 34 : Word W) + 5 * (siteNo : Word W) := by
    simp only [kern, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  let known:=emit ⟨fun k=>(postHigh _ (by omega)).trans (lib.words k)⟩
    ((retainedKernel _ facts.2.1).trans kernelWord) kguard
    (fun a=>(postHigh _ (area.trans (locK a).1)).trans (oldArchive _ (locK a).1 (locK a).2))
    (fun a=>(postHigh _ (area.trans (locI a).1)).trans (oldArchive _ (locI a).1 (locI a).2))
    geometry footprint (demandKeep resumeArchive)
  let paired:=HistoryGatherExecution.ReadPage.memory known.1
  let pg:=HistoryGatherExecution.ReadPage.start known.1
  let armLayout:=maps i j
  let armSite:=((roles i) j).val
  let dp:=(Fintype.equivFin (demandGraph.Port armSite)).symm
  let sp:=(Fintype.equivFin (supplyGraph.Port armSite)).symm
  let nativeWidths:=known.2.2.1
  have limits:=gathered_party_limits (u:=u) (A:=armLayout) («D»:=demandGraph) (G:=ShrinkMotif.supply)
    (j:=armSite) (base:=baseWidth (row i)) (live:=PhysicalShrink.b P oldWidth₀ (shrinkRecordCode s rem A) hc (row i))
    (tile:=entries (row i)) (dp:=dp) (sp:=sp) (di:=fun k=>(dp k).val.1.val) (si:=fun k=>(sp k).val.1.val)
    (v:=hist (row i)) paired pg known.1 age page.2.2 nativeWidths.2.2.2.1 nativeWidths.2.2.2.2
    (fun k=>PhysicalShrink.fits B.shrink P oldWidth₀ (shrinkRecordCode s rem A) hc (row i) _)
  have banks:PhysicalBanks u armLayout:=((PhysicalBanks.layout u arch f).withMotif i.val).withParty armSite.val
  have idFits : (HistoryNodePorts.id armLayout.nodePorts).Fits W (fun _=>0) (numeric paired) (fun _=>0):=
    ⟨⟨trivial,by change base u 18<2^W;omega⟩,trivial,(paired _).isLt,Nat.one_lt_two_pow (by omega)⟩
  have nodeValue:(HistoryNodePorts.id armLayout.nodePorts).value (fun _=>0) paired (fun _=>0)=(node:Word W):=by
    have e:=Formula.value_eq_natural (HistoryNodePorts.id armLayout.nodePorts) (fun _=>0) (numeric paired)
      (fun _=>0) idFits
    rw [word_numeric] at e
    change _ = ((numeric paired (base u 18) - 1 : ℕ) : Word W) at e
    exact e.trans (congrArg (fun n : ℕ => (n : Word W))
      (show numeric paired (base u 18) - 1 = node from postCurrent))
  let pos:=(tileNo i).val*6+armSite.val
  let kg:=(f).kinds+7*pos
  have from18:base u 18≤base u 19:=(Nat.le_add_right _ _).trans (TickWorkspace.apart (u:=u) (by decide:18<19))
  have issuedRow:=recorded_fields B s D rem hD small A cur ctr before issued final paired c branch hdr H saved
    v order i armLayout oldCap baseRoom wide icRoom offset postIncident joints
    (fun a=>(postHigh _ (area.trans (locI a).1)).trans (oldArchive _ (locI a).1 (locI a).2)) armSite
  have shape : wordAt paired (selected armLayout paired).incident 2=((tileNo i).val:Word W) :=
    (Fin.cast_val_eq_self _).symm.trans (congrArg (fun n:ℕ=>(n:Word W)) issuedRow.2.1)
  have pages:=Mounted.selected_pages (B:=B) (G:=shrinkGrid B level) (pre:=pref)
    (m:=paired) armLayout (tileNo i) armSite rfl rfl rfl rfl rfl rfl rfl shape
  have kindPointer : (selected armLayout paired).kindPage=(kg:Word W):=pages.1
  have kindLow:base u 18≤kg:=by
    change _≤Mounted.base B height start pref+7*pos
    unfold Mounted.base gridStart;omega
  have pageLow:base u 18≤pg:=by
    change _≤Mounted.base B height start pref+7*(shrinkGrid B level).rows.length+(shrinkGrid B level).stride*pos
    unfold Mounted.base gridStart;omega
  have seenReads : PartyReads u armLayout paired pg :=
    PartyReads.of_rows rfl rfl (by have:=nw.1;have:=TickWorkspace.apart (u:=u) (by decide:18<44);omega)
      (by have:=nw.1;omega) nodeValue (retainedKernel _ facts.2.1) postIncident kindPointer
      (by have:=kw.1;omega) (by have:=iw.1;omega) permanent.1
      ((from18.trans (area.trans kmin)).trans (Nat.le_add_right _ (5*siteNo)))
      ((from18.trans (area.trans rmin)).trans
        (Nat.le_add_right _ (6*(Incidents.capacity S*siteNo+i.val)))) kindLow pageLow
  have pageHeadRoom: pg+HistoryPortCatalogue.headerBase armLayout.demandCap armLayout.supplyCap<2^W:=
    (Nat.add_le_add_left pageHeaderFits pg).trans_lt permanent.2.1
  have stageHigh (j:Fin 9) : base u 18≤(paired (selected armLayout paired).kernel.val+(j.val:Word W)).val:=by
    have kernel : (paired (selected armLayout paired).kernel.val).val=c.header:=known.2.2.2.1
    have addr:=H.cursor.header.fit
    have small:=j.isLt
    rw [←Fin.cast_val_eq_self (paired (selected armLayout paired).kernel.val),kernel,
      ←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    exact from18.trans (headHigh.trans (Nat.le_add_right ..))
  have issuedHigh (side:Bool) (k:ℕ) (hk:k<HistoryGatherExecution.cap armLayout side)
      (portEnabled:portActive armLayout paired side k) : base u 18≤ issuedCell armLayout paired side k := by
    let ptr:=pointers K c dims₀
    obtain ⟨choices,supply,demands,_⟩:=H.cursor.allocated
    have next {a b n : ℕ} (span : b=a+n) : a≤b := (Nat.le_add_right _ _).trans_eq span.symm
    have supplyLow : base u 18≤ptr.supply :=
      ((from18.trans (area.trans heapHigh)).trans_eq choices.symm).trans (next supply)
    have demandLow : base u 18≤ptr.demands := supplyLow.trans (next demands)
    have bounds:=recorded_port_limits B s D rem hD small A cur ctr before issued final paired c branch hdr H saved
      v order i armLayout oldCap baseRoom wide icRoom offset postIncident joints
      (fun a=>(postHigh _ (area.trans (locI a).1)).trans (oldArchive _ (locI a).1 (locI a).2))
      level armSite pg (arity B) (base u 18) (max demandCap top) known.1 known.2.1 rfl rfl rfl rfl
      rfl Kpos Kfit geometry known.2.2.2.1 (demandKeep resumeArchive)
      (fun e=>(demandWidth_le P oldWidth₀ (motifNumbers P (shrinkRecordCode s rem A) hc)
        (prior_width_le s rem A) (row i) e).trans (Nat.le_max_left demandCap top))
      (fun e=>(issuedSize (row i) e).trans (Nat.le_max_right demandCap top)) (max_lt demandFits topWord)
      demandLow supplyLow
    exact bounds.2 side k hk portEnabled
  have headerSafe {size:ℕ} (space:PartySpace u armLayout paired node pg size) :=
    space.header seenReads rfl known.1.base known.1.extent stageHigh issuedHigh
  -- Source-map bank and numerical bounds.
  have space:=PartySpace.of_banks banks age nr availableAt armSite.isLt budget headSize limits.1
    seenReads pageHeadRoom nodeValue
  have pairHead:=(elected_arm _ _ _ _ _ _ _ _ _ _ _ _ facts.1).2.1 (1:Fin 4)
  have mapCount:=space.mapCount known.2.1 pairHead
  let trees:=Children.join 0 count (fun _=>p) (fun _ k=>.pin k) (fun k=>piece (row k))
  have one:=Finset.single_le_sum («f»:=fun k:Fin count=>(piece (row k)).resources+p)
    (fun k _=>Nat.zero_le _) (Finset.mem_univ i)
  have budgetTree:=trees.charge_eq
  have sharedCost {pins n : ℕ} {tree : Tree F pins} (C : TariffChildren tree n) :
      C.shared+1≤tree.resources :=
    (Nat.le_add_right (C.shared+1) _).trans_eq C.native.charge_eq.symm
  have shared : (bundle i).shared+1≤(piece (row i)).resources := sharedCost (bundle i)
  have combined : 2+p+(bundle i).shared≤2^W := by
    change (siteTree).resources=0+1+∑k:Fin count,((piece (row k)).resources+p) at budgetTree
    calc
      2+p+(bundle i).shared = 1+((bundle i).shared+1+p) := by
        change (1+1)+p+(bundle i).shared = _
        ac_rfl
      _ ≤ 1+((piece (row i)).resources+p) := Nat.add_le_add_left (Nat.add_le_add_right shared p) 1
      _ ≤ 1+∑k:Fin count,((piece (row k)).resources+p) := Nat.add_le_add_left one 1
      _ = (siteTree).resources := budgetTree.symm
      _ ≤ 2^W := (Nat.le_mul_of_pos_left _ (by decide : 0<4)).trans (siteSize.trans upper.le)

  have paidPairCells {a b limit : ℕ} (left : Tree F a) (right : Tree F b)
      (rows : 8*(left.rows+right.rows)≤limit) : 4*(Tree.pair left right).compile.cells≤limit := by
    rw [Tree.compiled_rows, Tree.pair_rows]
    exact (Nat.mul_le_mul_right _ (by decide : 4≤8)).trans rows
  have pairCellRoom := paidPairCells _ _ rowSpace
  let issuedRun:=known.2.2.2.2.2
    (fun q bit scratch frame=>recorded_old_source_cells (B:=B) (level:=level) (u:=u) (start:=start) (height:=height)
      (K:=K) (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt) (previous:=previous)
      (successor:=successor) (v:=v) (order:=order) (node:=node) (input:=input) H priorWords ordered layoutEq
      priorSites T₀ nodeId nodeBase cacheBase degree₀ cached age nr cursor childCap prefixRoom
      (by change WordLayout.prior previous ((P).placement lay) children childOrder v+successor.ports.halfBits v<2^W at pinRoom;omega)
      oldRows directory childPtr childTable arr childIds i j scratch (sourceRead scratch frame).1 (sourceRead scratch frame).2.1 q bit)
    (fun q bit scratch frame=>recorded_fresh_source_cells (B:=B) (level:=level) (u:=u) (start:=start) (height:=height)
      (K:=K) (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt) (previous:=previous)
      (successor:=successor) (v:=v) (order:=order) (node:=node) (input:=input) cur ctr before issued final c hdr H saved
      ⟨heapHigh,area.trans heapHigh⟩ (fun a lo=>guard a (heapHigh.trans lo)) (fun a lo=>oldArchive a (heapHigh.trans lo))
      T₀ nodeId nodeBase cacheBase countNew orderNew degree₀ cached newBits headAt age nr cursor childCap prefixRoom
      degreeFit oldCap.residual pinRoom privRoom i j startM privateRows widthRoom scratch (sourceRead scratch frame).1
      (sourceRead scratch frame).2.1 (sourceRead scratch frame).2.2 q bit)
    space.positive space.resident space.hSize limits.2.1 mapCount space.mapRoom space.range (headerSafe space)
    space.keep space.clear space.headAt limits.2.2.1 limits.2.2.2
    (fun _ _=>gather_source_room combined _) (fun _ _=>gather_source_room combined _) space.atNode space.fitsAddress
    (space.clearPair _ space.mapBase _ pairCellRoom)
  show ∃ w,ArmWrite.Real u node encode (maps i j) ((nets i) j) ((bundle i).wire j) now w ∧
    w.ticks+HistoryGatherExecution.tariff W (maps i j) w.plan≤rate i j from by
    have win:=PartyWindow.of_layout arch f i.val ((roles i) j).val.val age availableAt ((roles i) j).val.isLt budget
    have paid:=CapturedArm.paid (issued:=issuedRun) (ref:=reference) (mode:=rfl) (dem:=rfl) (sup:=rfl)
      (loc:=win) («count»:=countSpace) (gates:=rowSpace) (pins:=pinSpace)
    have chosen : B.shrink.row (tileNo i) =
        PhysicalShrink.picked B.shrink P oldWidth₀ (shrinkRecordCode s rem A) hc (row i) :=
      B.shrink.row_chosen _
    let rowPrice (r₀ : B.shrink.Row) : ℕ :=
      let cell := recordedRoleAt B.shrink r₀ armSite
      partyRate cell*(W+1)^3*(1+many (row i)) + partyMapRate reference cell*(1+many (row i))
    obtain ⟨w,real,cost⟩ := paid
    exact ⟨w,real,cost.trans_eq (congrArg rowPrice chosen.symm)⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
omit [Fintype F] in
/-- Recover the exact arity seen by the shrink join from the physical child
prefix read and its selected successor site, in the archive's actual active-motif order. -/
theorem recorded_root_width (cur : Word W) (before issued : Memory W) (c : Cursor)
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (L : A.Words Pins) (z : ((M).next branch).Site)
    (ordinal : shrinkPackOrder s D rem A v=shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))
    (C : HistoryNodePorts.Layout) («cap» : ℕ) (Q : HistoryStageRoot.Input) (raw : ℕ→ℕ)
    (current : raw C.cursor-1=Q.id) (nodes : C.nodes=Q.nodeBase) (cache : C.cache=Q.resultBase) :
    let step:=shrinkBinary_assembler B.shrink s D rem hD small A L branch
    let fresh:=(((M).target_eq branch).symm ▸ step.words.ports : PortLayout ((M).rules.target branch) Pins)
    let target:=Move.WordStep.targetSite (R:=M) (i:=branch) z
    HistoryStageRoot.Ports L.ports fresh step.stage.count step.stage.child target Q raw →
    step.stage.count target ≤ «cap» →
    childWidth C «cap» raw (C.starts+«cap»)+((M).next branch).incidentWidth z=
      (issuedRootAt B.shrink s D rem hD small A L branch v order).1 := by
  intro step fresh target portsSeen bounded
  have width:=HistoryStageSetup.complete_port_width L step z Q raw C «cap» portsSeen current nodes cache bounded
    (shrinkBinary_assembler_arity B.shrink s D rem hD small A L branch target)
  exact width.trans (congrArg Sigma.fst (shrink_word_root_at B.shrink s D rem hD small A L branch z v
    ordinal order (ShrinkOutput.rootKeys B.shrink s D rem hD small A H)))

open private executeSiteRun from OAI.ThreeFlat.RAM.HistoryShrinkSiteExecution

private theorem retime_execution {width oldTicks newTicks : ℕ}
    (procedure : Procedure width) (before after : Memory width)
    (ticks : oldTicks = newTicks) (exec : procedure.Exec before after oldTicks) :
    procedure.Exec before after newTicks := by
  subst newTicks
  exact @exec

set_option maxRecDepth 18000 in
set_option maxHeartbeats 1800000 in
private theorem recorded_slot_joined (i : Fin count) (m : Memory W) :
    ((run).slot i.val m).joined = (piece (row i)).compile := by
  have occupied := recordedSite_occupied B level u start height K rem hD small A branch gt
    previous successor v order node i m
  have native := tariffIssuedSlot_eq (F:=F) («W»:=W) (u:=u) (node:=node)
    encode (cloud i) (active i) (bundle i) (rate i) m
  exact (congrArg SiteSlot.joined (occupied.trans native.symm)).trans
    ((bundle i).native.joined (issuedRows i m))

set_option maxRecDepth 18000 in
set_option maxHeartbeats 8000000 in
private theorem assemble_recorded_site (age : 16≤u) (nr : node<V₁^2) (capRoom : cap+1≤V₁)
    (available : count≤(J).party.motifs)
    (stat : ((f).motifs+2)*((f).parties+2)*8*32≤V₁)
    (size : 4*(siteTree).resources≤V₁) (pins : p<2^W)
    (tags : ∀ arg : (Fin 3→Bool)→F, encode arg<2^W)
    (startRun : (HistoryNodePorts.phase W (J).nodePorts cap).Exec input first (HistoryNodePorts.phaseCost cap))
    (occupied : ∀ i : Fin count,seen (atSlot i.val) →
      (slot i (atSlot i.val)).Live node encode (atSlot i.val) ∧
      (slot i (atSlot i.val)).ArmSpace node encode (atSlot i.val) u ∧ paidAt i (atSlot i.val))
    (padded : ∀ g : Fin (f).motifs,count≤g.val → seen (atSlot g.val) →
      let Z:=emptySlot (F:=F) («W»:=W) («p»:=p) (bank g)
      Z.Live node encode (atSlot g.val) ∧ Z.ArmSpace node encode (atSlot g.val) u)
    (queries : ∀ (k : Fin (f).motifs) (group : Bool) (μ : Memory W), seen μ →
      let G:=withMotif J k.val
      Protected (joinHeader G W group) μ (G.party.seed+64) (HistoryMotifJoin.rows G W group).length ∧
      (HistoryNodePorts.id G.nodePorts).value (fun _=>0) μ (fun _=>0)=(node:Word W) ∧
      (selected G μ).oldBits+(selected G μ).newBits=(p:Word W) ∧
      wordAt μ (selected G μ).kernel 3=(count:Word W)) :
    let ticks:=(run).cost node encode first compiled (HistoryNodePorts.phaseCost cap)
    (kernelProcedure J W cap).Exec input Xexec ticks ∧
    HistoryCompiledRows.Records encode (siteTree).compile (resultBank J node false 0) Xexec ∧
    (∀ j : Fin 4,Xexec (resultBank J node false 1+j.val)=
      ((HistoryBoundedJoin.Info.mk (resultBank J node false 0) p (siteTree).compile.cells (siteTree).compile.internal).words j:Word W)) ∧
    (∀ a,OutsideNode u node a→Xexec a=input a) ∧
    (∀ i : Fin count,paidAt i (atSlot i.val)) := by
  let banks:=PhysicalBanks.layout u arch f
  let roster:=recorded_roster B level u start height K rem hD small A branch gt
    previous successor v order node input age nr capRoom available occupied padded
  let zero : Fin (f).motifs:=⟨0,by change 0<8*d^2*2^(2*d+1);positivity⟩
  let facts:=queries zero false (atSlot (J).party.motifs) roster.2.2
  have outer : Chart J false node (atSlot (J).party.motifs) compiled
      (fun (_ : Fin count) (j : Fin p)=>(BitSource.pin j : BitSource 0 p)) encode := by
    as_aux_lemma =>
      exact activeTree_chart (partySite P lay) v order.equiv (fun m=>piece m.val) _ encode
        banks age nr stat rfl available size pins tags facts.1 facts.2.1 facts.2.2.1 facts.2.2.2
  let costEq:=HistoryNodePorts.phase_ticks W (J).nodePorts cap
  let emitted:=executeSiteRun J run (fun i : Fin count=>piece (row i)) node encode first
    (fun i=>recorded_slot_joined B level u start height K rem hD small A branch gt
      previous successor v order node i (atSlot i.val))
    banks S rfl cap input (show cap≤V₁ from (Nat.le_succ _).trans capRoom)
    (by
      exact @retime_execution _ _ _ (HistoryNodePorts.phase W (J).nodePorts cap)
        input first costEq.symm (by exact @startRun)) rfl available
    (fun j=>(roster.1 j).1) (fun j=>(roster.1 j).2) outer
  exact ⟨(by
      exact @retime_execution _ _ _ (kernelProcedure J W cap) input Xexec
        (congrArg (fun charge=>(run).cost node encode first compiled charge) costEq) (by exact emitted.1)),
    emitted.2.1,emitted.2.2.1,emitted.2.2.2,roster.2.1⟩

set_option maxRecDepth 18000 in
set_option maxHeartbeats 8000000 in
/-- Evaluate the actual cached incidence program on a chronological shrink row.
The source and mask probes use the cursor and archived arrays on the current
RAM. The same state supplies both the private prefix and the later child maps. -/
theorem recorded_site_exec (cur ctr : Word W) (before issued final : Memory W) (c : Cursor) (hdr : ℕ)
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved : SavedFrame cur ctr hdr (en c).next.header (en c).next.heap issued final)
    (caps : ShrinkNativeCaps B.shrink s D rem W A) (rawArrays : RecordedArrayBounds W hdr c A)
    (controlsApart : cur.val<ctr.val)
    (headerOld : ∀a,c.header≤a→a<c.header+34→input a=final a)
    (strPos : 0<K) (strRoom : K<2^W)
    (oldArchive : ∀a,hdr≤a→a<(en c).next.heap→input a=final a)
    (area : base u 19≤hdr) (current : numeric input (base u 18)=node+1)
    (age : 16≤u) (nr : node<V₁^2) (intrinsic : blockPageRate B≤u)
    (romHigh : base u 19 ≤ start) (romFit : start+libraryWords B height<2^W)
    (pins : p<2^W)
    (size : 4*(siteTree).resources≤V₁)
    (z : ((M).next branch).Site)
    (halfBefore : State.HalfRows (shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch)
      (fun a=>base u 19≤a ∧ a<2^W) (numeric input))
    (atNode : let O:=shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch
      node=O.layer.first+(O.ord z).val ∧ (O.ord z).val=siteNo)
    (b : NavigationNodeRows.Banks) (nodeBase : b.nodes=base u 44)
    (dir : let O:=shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch
      HistoryStageSetup.DirectoryRow b O.layer (O.ord z) input)
    (data : NavigationNodeRows.LayerData (nodeLayer K c (.shrink dims₀)))
    (read : data.Reads (numeric input))
    (cells : data.Footprint (fun a=>base u 19≤a ∧ a<2^W) (numeric input))
    (childrenSmall : ∀ k, data.child
      ((shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch).ord z) k<V₁^2)
    (totalPorts : childWidth (J).nodePorts cap (numeric input) ((J).nodePorts.starts+cap)+
      ((M).next branch).incidentWidth z=p)
    (elected : ∀ (i : Fin count) (j : Fin (recordedRoleCount (active i))) (startM now : Memory W),seen startM →
      ArmRead u node cap (cloud i) input startM now→
      PrivateSite (geo:=S) (cloud i) startM (owns i) (widths i)→
      ∃ w,ArmWrite.Real u node encode (maps i j) ((nets i) j) ((bundle i).wire j) now w ∧
        w.ticks+HistoryGatherExecution.tariff W (maps i j) w.plan≤rate i j) :
    let ticks:=(run).cost node encode first compiled (HistoryNodePorts.phaseCost cap)
    (kernelProcedure J W cap).Exec input Xexec ticks ∧
    HistoryCompiledRows.Records encode (siteTree).compile (resultBank J node false 0) Xexec ∧
    (∀ j : Fin 4,Xexec (resultBank J node false 1+j.val)=
      ((HistoryBoundedJoin.Info.mk (resultBank J node false 0) p (siteTree).compile.cells (siteTree).compile.internal).words j:Word W)) ∧
    (∀ a,OutsideNode u node a→Xexec a=input a) ∧
    (∀ i : Fin count,paidAt i (atSlot i.val)) := by
  let banks:=PhysicalBanks.layout u arch f
  let gr:=shrinkGrid B level
  have inGrid : gr∈grids B:=List.mem_append_left _ (List.mem_ofFn.mpr ⟨level,rfl⟩)
  have rateBound := (grid_page_rate_le_block B inGrid).trans intrinsic
  have uw : u≤u^10:=Nat.le_self_pow (by decide) u
  have seq : u<V₁:=uw.trans_lt Nat.lt_two_pow_self
  have wpos : 8≤W:=by omega
  have wide:=wpos
  have smallV : V₁<2^W:=Nat.pow_lt_pow_right (by decide) (by omega)
  have vpos : 128≤V₁:=by change 2^7≤2^(u^10);exact Nat.pow_le_pow_right (by decide) (by omega)
  have stat : ((f).motifs+2)*((f).parties+2)*8*32≤V₁:=by
    change (gr.motifs+2)*(gr.parties+2)*8*32≤V₁
    unfold gridPageRate at rateBound;omega
  have motifRoom : (f).motifs+1≤V₁:=by
    have h:=Nat.le_mul_of_pos_right ((f).motifs+2) (by omega : 0<(f).parties+2)
    omega
  have icRoom : Incidents.capacity S<2^W:=(show Incidents.capacity S≤V₁ by change (f).motifs≤V₁;omega).trans_lt smallV
  have capRoom : cap+1≤V₁:=by
    have h : d≤8*d^2:=by have := Nat.le_self_pow (by decide : 2≠0) d;omega
    have := Nat.mul_le_mul_right (2^(2*d+1)) h
    change 8*d^2*2^(2*d+1)+1≤V₁ at motifRoom
    change d*2^(2*d+1)+1≤V₁;omega
  have headSize : 3+5*(f).demands+4*(f).supplies≤V₁:=by
    change 3+5*gr.demand+4*gr.supply≤V₁
    unfold gridPageRate at rateBound;omega
  have earlier:=apart (u:=u) (by decide : 18<19)
  have square : 32*V₁≤V₁^2:=by rw [pow_two];exact Nat.mul_le_mul_right V₁ (by omega)
  have quart : V₁^2≤V₁^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have reserve : base u 14+2*V₁+26 ≤ start:=by
    have before:=apart (u:=u) (by decide : 14<19)
    change base u 14+V₁^4≤base u 19 at before;omega
  have regs:=mounted_arch_registers B (u:=u) (start:=start) (height:=height)
    (show archiveWindow u start (libraryWords B height) from ⟨romFit,.inr (by omega)⟩)
  have counts : (arch).counts+1<2^W:=by
    change start+StableCompactROMNative.size height+staticSize B+1<2^W
    unfold libraryWords HistoryCompactorCounts.size at romFit
    omega
  have lookup : (arch).lut+1<2^W:=by
    change start+StableCompactROMNative.size height+1<2^W
    change start+StableCompactROMNative.size height+staticSize B+1<2^W at counts
    omega
  have lutStride:=(regs.2.1)
  have pageStart:=(regs.2.2.1)
  have pageStride:=(regs.2.2.2.1)
  have lutAway : base u 14+2*V₁+26≤(arch).lut:=by change _ ≤ start+_;omega
  have countsAway : base u 14+2*V₁+26≤(arch).counts:=by change _ ≤ start+_+_;omega
  have privRoom : (J).privateStarts+9<2^W:=by
    have bound : base u 18+V₁^4<2^W := word_space (u:=u) (i:=18) (by omega)
      (show 18<V₁^4 from by omega)
    change base u 18+4*V₁+9<2^W
    omega
  have portRoom : HistoryGatherExecution.portsEnd J<2^W:=by
    have bound : base u 17+V₁^4<2^W := word_space (u:=u) (i:=17) (by omega)
      (show 17<V₁^4 from by omega)
    have q : 1+(f).demands+(f).supplies≤V₁:=by omega
    have mul:=Nat.mul_le_mul_right V₁ q
    change base u 17+(1+(f).demands+(f).supplies)*V₁<2^W
    rw [←pow_two] at mul
    omega
  have tags (arg : (Fin 3→Bool)→F) : encode arg<2^W :=
    (Fintype.equivFin _ arg).isLt.trans_le (block_tags_at_age B intrinsic)
  let oldCap:=caps.1
  have baseRoom:=caps.2.1
  have offset:=rawArrays.widthPos
  have oldArrays:=rawArrays.toOldArrayBounds
  have headAbove:=rawArrays.header_at
  have ctrlBound:=(H.cursor.controls.trans_lt controlsApart).le
  have cursor : numeric input (base u 18)-1=node:=by rw [current];omega
  have heapAfter : hdr≤c.heap:=oldArrays.graphLow.trans ((Nat.le_add_right _ _).trans H.cursor.graph)
  have allocs:=descriptorAllocation K c (.shrink dims₀)
  have kmin : hdr≤fields₀ c 34:=heapAfter.trans allocs.1
  have rmin : hdr≤fields₀ c 36:=heapAfter.trans allocs.2.2.1
  let issuedSites:=shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch
  have chosenID : node=issuedSites.layer.first+(issuedSites.ord z).val:=atNode.1
  have ordEq : (issuedSites.ord z).val=siteNo:=atNode.2
  have original : input (base u 44+8*node+5)=((fields₀ c 34+5*siteNo:ℕ):Word W) := by
    rw [←nodeBase,chosenID,dir.kernel,←ordEq,Nat.mul_comm 5]
    rfl
  have halfSource : numeric input (base u 44+8*node+6)=issuedSites.layer.incident+(issuedSites.ord z).val*2 := by
    change (input _).val=_
    rw [←nodeBase,chosenID,dir.incident,Fin.val_cast_of_lt (by simpa using (halfBefore.headerSafe z 0).2)]
  have numChildren : numeric input (base u 44+8*node+4)=cap := by
    change (input _).val=_
    rw [←nodeBase,chosenID,dir.childCount]
    exact Fin.val_cast_of_lt ((by omega : cap<V₁).trans smallV)
  have startRun : (HistoryNodePorts.phase W (J).nodePorts cap).Exec input first (HistoryNodePorts.phaseCost cap) := by
    as_aux_lemma =>
      let phaseExec (bound : ℕ) : Prop :=
        (HistoryNodePorts.phase W (J).nodePorts bound).Exec input
          (fillSegment (J).nodePorts.starts (bound+1)
            (fun a=>(childWidth (J).nodePorts bound (numeric input) a:Word W)) input)
          (HistoryNodePorts.phaseCost bound)
      have archived : phaseExec issuedSites.layer.childCount := by
        intro programs registers slots
        have childRun := @HistoryShrinkEmitter.child_starts_archive u J input issuedSites.layer data (issuedSites.ord z)
          banks rfl age vpos (chosenID ▸ nr) (by change 0<d*2^(2*d+1);positivity)
          (by change cap≤V₁;omega) b nodeBase (chosenID ▸ current) dir read cells childrenSmall programs registers slots
        simpa only [childPrefix, HistoryNodePorts.phase_ticks] using childRun
      have issuedCap : issuedSites.layer.childCount = cap := rfl
      change phaseExec cap
      rw [← issuedCap]
      exact @archived
  have available : count≤(J).party.motifs :=
    (ShrinkOutput.selected_kernel B.shrink s D rem hD small A cur before c branch H oldCap baseRoom wide
      icRoom offset v 0).2.2
  have vbig : 128≤V₁:=by
    change 2^7≤2^(u^10)
    exact Nat.pow_le_pow_right (by decide) ((by omega : 7≤u).trans (Nat.le_self_pow (by decide) _))
  let siteChart:=shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch
  let kernelBase:=fields₀ c 34+5*siteNo
  let rowAddr (j : ℕ):=fields₀ c 36+6*(Incidents.capacity S*siteNo+j)
  have guard (a : ℕ) (_ : hdr≤a) (le : a<(en c).next.heap) : a≠cur.val ∧ a≠ctr.val :=
    ⟨(le.trans_le H.cursor.controls).ne,(le.trans_le ctrlBound).ne⟩
  have endRoom : (en c).next.heap<2^W:=H.cursor.controls.trans_lt cur.isLt
  have arrayHi (a : ℕ) (lo : hdr≤a) (hi : a<(en c).next.heap) :
      input a=issued a :=
    (oldArchive a lo hi).trans (saved _ (guard _ lo hi).1 (guard _ lo hi).2 (.inr lo) hi)
  have high {μ : Memory W} (state : seen μ) (a : ℕ) (after : base u 19≤a) :
      μ a=input a := state.retained a (outside_of_region node age nr (.inr (.inl after)))
  have bigHeap : c.heap ≤ (en c).next.heap := by rw [heap_step]; omega
  have afterHeap : hdr≤c.heap:=oldArrays.graphLow.trans ((Nat.le_add_right _ _).trans H.cursor.graph)
  have geom {μ : Memory W} (state : seen μ) : GeometryFrame dims₀ (pointers K c dims₀) issued μ := by
    as_aux_lemma =>
      apply GeometryFrame.of_intervals H.cursor
      · intro a lo hi
        have under : a<(en c).next.heap:=by have:=H.cursor.earlier;omega
        exact (high state a (headAbove.trans lo)).trans ((headerOld _ lo hi).trans
          (saved _ (under.trans_le H.cursor.controls).ne (under.trans_le ctrlBound).ne
            (.inl (by change a<c.header+64;omega)) under))
      · intro a lo hi
        have lower:=oldArrays.graphLow.trans lo
        exact (high state a (area.trans lower)).trans (arrayHi _ lower ((hi.trans_le H.cursor.graph).trans_le bigHeap))
      · intro a lo hi
        have lower:=oldArrays.widthLow.trans lo
        exact (high state a (area.trans lower)).trans (arrayHi _ lower ((hi.trans_le H.cursor.widths).trans_le bigHeap))
      · intro a lo hi
        have lower:=afterHeap.trans lo
        exact (high state a (area.trans lower)).trans (arrayHi _ lower hi)
  have kernelBounds (j : Fin 5) : hdr≤kernelBase+j.val ∧ kernelBase+j.val<(en c).next.heap := by
    have read:=ShrinkOutput.selected_kernel B.shrink s D rem hD small A cur before c branch H oldCap baseRoom
      wide icRoom offset v j
    exact ⟨by dsimp [kernelBase];omega,by simpa only [kernelBase,Nat.add_assoc] using read.1⟩
  have kernelWord {μ : Memory W} (state : seen μ) (j : Fin 5) : μ (kernelBase+j.val)=
      ((![c.header,siteNo,1,count,fields₀ c 36+siteNo*(6*Incidents.capacity S)]:Fin 5→ℕ) j:Word W) := by
    obtain ⟨lo,hi⟩:=kernelBounds j
    rw [high state _ (area.trans lo),arrayHi _ lo hi]
    simpa only [kernelBase,Nat.add_assoc] using
      (ShrinkOutput.selected_kernel B.shrink s D rem hD small A cur before c branch H oldCap baseRoom
        wide icRoom offset v j).2.1
  have curNow {μ : Memory W} (state : seen μ) : numeric μ (base u 18)-1=node:=by
    change (μ (base u 18)).val-1=_
    rw [state.retained _ (outside_of_region node age nr (.inr (.inr (.inl rfl))))]
    exact cursor
  have nodeEnd:=directory_address_space (u:=u) age vbig nr
  have far:=apart (u:=u) (by decide : 19<44)
  have controls:=apart (u:=u) (by decide : 18<19)
  have getId {μ : Memory W} (state : seen μ) :
      (HistoryNodePorts.id (J).nodePorts).value (fun _=>0) μ (fun _=>0)=(node:Word W) := by
    have ff : (HistoryNodePorts.id (J).nodePorts).Fits W (fun _=>0) (numeric μ) (fun _=>0):=
      ⟨⟨trivial,by change base u 18<2^W;omega⟩,trivial,(μ (base u 18)).isLt,by change 1<2^W; omega⟩
    have eval:=(HistoryNodePorts.id (J).nodePorts).value_eq_natural (fun _=>0) (numeric μ) (fun _=>0) ff
    simpa only [word_numeric,Fin.cast_val_eq_self,Nat.cast_zero] using
      eval.trans (congrArg (fun n:ℕ=>(n:Word W)) (curNow state))
  have nd {μ : Memory W} (state : seen μ) := nodeAddress_at (u:=u) (A:=J) rfl (getId state)
  have field {μ : Memory W} (state : seen μ) (j : Fin 8) :
      wordAt μ (HistoryMotifJoin.nodeAddress (J).nodePorts μ) j.val=input (base u 44+8*node+j.val) := by
    rw [nd state,wordAt,←Nat.cast_add,Fin.val_cast_of_lt (by have:=j.isLt;omega)]
    exact high state _ (by omega)
  have kptr (k : ℕ) {μ : Memory W} (state : seen μ) :
      (selected (withMotif J k) μ).kernel=(kernelBase:Word W) := (field state 5).trans original
  have kw (k : ℕ) {μ : Memory W} (state : seen μ) (j : Fin 5) :
      wordAt μ (selected (withMotif J k) μ).kernel j.val=
      ((![c.header,siteNo,1,count,fields₀ c 36+siteNo*(6*Incidents.capacity S)]:Fin 5→ℕ) j:Word W) := by
    rw [kptr _ state,wordAt,←Nat.cast_add,Fin.val_cast_of_lt ((kernelBounds j).2.trans endRoom)]
    exact kernelWord state j
  have incident (k : ℕ) {μ : Memory W} (state : seen μ) :
      (selected (withMotif J k) μ).incident=(rowAddr k:Word W):=by
    change wordAt μ (selected (withMotif J k) μ).kernel 4+(6*k:ℕ)=_
    rw [show wordAt μ (selected (withMotif J k) μ).kernel 4=
      ((fields₀ c 36+siteNo*(6*Incidents.capacity S):ℕ):Word W) from kw k state 4,←Nat.cast_add]
    congr 1;dsimp [rowAddr];ring
  have range (i : Fin (f).motifs) (j : Fin 6) : hdr≤rowAddr i.val+j.val ∧
      rowAddr i.val+j.val<(en c).next.heap := by
    refine ⟨by dsimp [rowAddr];omega,?_⟩
    by_cases good : i.val<count
    · simpa only [rowAddr,Nat.add_assoc] using (ShrinkOutput.selected_descriptor B.shrink s D rem hD small A
        cur before c branch H oldCap baseRoom wide icRoom offset v order ⟨i.val,good⟩ j).1
    · simpa only [rowAddr,Nat.add_assoc] using (ShrinkOutput.selected_padding B.shrink s D rem hD small A
        cur before c branch H oldCap baseRoom wide icRoom offset v i (Nat.le_of_not_gt good) j).1
  have reads {i : Fin count} {μ : Memory W} (state : seen μ) :
      (∀ j:Fin 6,rowAddr i.val+j.val≠cur.val ∧ rowAddr i.val+j.val≠ctr.val ∧ hdr≤rowAddr i.val+j.val) ∧
      (∀ j:Fin 6,μ (rowAddr i.val+j.val)=final (rowAddr i.val+j.val)) := by
    have facts:=range (i.castLE available)
    exact ⟨fun j=>⟨(guard _ (facts j).1 (facts j).2).1,(guard _ (facts j).1 (facts j).2).2,(facts j).1⟩,
      fun j=>(high state _ (area.trans (facts j).1)).trans (oldArchive _ (facts j).1 (facts j).2)⟩
  have kg (j : Fin 5) : kernelBase+j.val≠cur.val ∧ kernelBase+j.val≠ctr.val ∧ hdr≤kernelBase+j.val :=
    ⟨(guard _ (kernelBounds j).1 (kernelBounds j).2).1,(guard _ (kernelBounds j).1 (kernelBounds j).2).2,(kernelBounds j).1⟩
  have kh {μ : Memory W} (state : seen μ) (j : Fin 5) :
      μ (kernelBase+j.val)=final (kernelBase+j.val) :=
    (high state _ (area.trans (kernelBounds j).1)).trans (oldArchive _ (kernelBounds j).1 (kernelBounds j).2)
  have kernelPointer (i : Fin count) (μ : Memory W) (state : seen μ) :
      (selected (withMotif J i.val) μ).kernel=(fields₀ c 34:Word W)+5*(siteNo:Word W) := by
    simpa only [kernelBase,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using kptr i.val state
  let shared (i : Fin count) (μ : Memory W) (state : seen μ) :=
    recorded_private B s D rem hD small A cur ctr before issued final μ c branch hdr H saved v order i
      (cloud i) oldCap baseRoom wide icRoom offset (reads (i:=i) state).1 (reads (i:=i) state).2
      (kernelPointer i μ state) rfl kg (kh state) (geom state) rfl rfl strPos strRoom
  have mask (i : Fin count) (μ : Memory W) (state : seen μ) :=
    recorded_party_order B s D rem hD small A cur ctr before issued final μ c branch hdr H saved v order i
      (cloud i) oldCap baseRoom wide icRoom offset (reads (i:=i) state).1 (reads (i:=i) state).2
      (kernelPointer i μ state) rfl rfl kg (kh state)
  have motifReads (i : Fin (f).motifs) {μ : Memory W} (state : seen μ) :
      MotifReadCells (bank i) μ (fun a=>base u 19≤a) := by
    apply MotifReadCells.of_addresses (bank i) kernelBase (rowAddr i.val) (kptr i.val state) (incident i.val state)
    · intro j;exact ⟨area.trans (kernelBounds j).1,(kernelBounds j).2.trans endRoom⟩
    · intro j;exact ⟨area.trans (range i j).1,(range i j).2.trans endRoom⟩
  have halves {μ : Memory W} (state : seen μ) :
      State.HalfRows siteChart (fun a=>base u 19≤a ∧ a<2^W) (numeric μ) :=
    halfBefore.transfer (fun a bounds=>congrArg Fin.val (high state a bounds.1)) (fun _ h=>h)
  have halfPtr {μ : Memory W} (state : seen μ) :
      wordAt μ (HistoryMotifJoin.nodeAddress (J).nodePorts μ) 6=((siteChart.layer.incident+(siteChart.ord z).val*2:ℕ):Word W) := by
    calc
      _ = input (base u 44+8*node+6) := field state ⟨6,by decide⟩
      _ = ((numeric input (base u 44+8*node+6):ℕ):Word W) := (Fin.cast_val_eq_self _).symm
      _ = _ := congrArg (fun n : ℕ => (n:Word W)) halfSource
  have nodeReads {μ : Memory W} (state : seen μ) :=
    NodeReadCells.of_archive (A:=J) siteChart z age vbig (by exact Nat.two_pow_pos _) node nr rfl
      (nd state) (halves state) (halfPtr state)
  have childNum {μ : Memory W} (state : seen μ) :
      (wordAt μ (HistoryMotifJoin.nodeAddress (J).nodePorts μ) 4).val=cap :=
    (congrArg Fin.val (field state ⟨4,by decide⟩)).trans numChildren
  have portFit {μ : Memory W} (state : seen μ) :
      (selected J μ).oldBits+(selected J μ).newBits=(p:Word W) := by
    as_aux_lemma =>
      let Q:=HistoryStageBody.numInput J cap (numeric input)
      have Qn : HistoryStageRoot.node Q=base u 44+8*node := by
        change base u 44+8*(numeric input (base u 18)-1)=_
        rw [cursor]
      have cnt : HistoryStageRoot.childCount Q (numeric μ)=cap:=by
        rw [HistoryStageRoot.childCount,Qn];change (μ _).val=_;rw [high state _ (by omega)];exact numChildren
      have cur : HistoryMotifJoin.nodeAddress (J).nodePorts μ=(HistoryStageRoot.node Q:Word W) := Qn.symm ▸ nd state
      have source : numeric μ (HistoryStageRoot.node Q+6)=siteChart.layer.incident+(siteChart.ord z).val*2:=by
        rw [Qn];change (μ _).val=_;rw [high state _ (by omega)];exact halfSource
      have room : (J).nodePorts.starts+cap<2^W := by
        have limit : base u 18+4*V₁+9<2^W := privRoom
        change base u 18+3*V₁+cap<2^W
        omega
      rw [←totalPorts]
      exact selected_port_total siteChart z Q ((halves state).transfer (fun _ _=>rfl) (fun _ h=>h.2))
        cur (by rw [Qn];omega) source _ (by rwa [cnt]) (by rw [cnt];exact state.child ⟨cap,by omega⟩)
        (by exact Nat.two_pow_pos _)
  have marked (g : Fin (J).party.motifs) (μ : Memory W) (state : seen μ) :
      Protected (privateHeader (bank g) W) μ (J).privateStarts 9 := by
    as_aux_lemma =>
      apply privateHeader_physical (banks.withMotif g.val) vbig (nodeReads state) (motifReads g state)
      have stage : μ (selected (bank g) μ).kernel.val=(c.header:Word W) := by
        have cell := kw g.val state (0 : Fin 5)
        change μ ((selected (bank g) μ).kernel+((0:ℕ):Word W)).val=(c.header:Word W) at cell
        simpa only [Nat.cast_zero,add_zero] using cell
      by_cases live : g.val<count
      · let i : Fin count:=⟨g.val,live⟩
        exact shrinkPrivateCells_at_stage (shared i μ state) K c dims₀ headAbove H.cursor.earlier endRoom.le
          stage rfl
      · have ptr : (μ (selected (bank g) μ).kernel.val).val=(pointers K c dims₀).ownHeader := by
          rw [stage,Fin.val_cast_of_lt (by have h:=H.cursor.earlier;omega)]
          rfl
        let view:=H.reopenAt μ (geom state) (selected (bank g) μ).kernel ptr
        let supply:=(pointers K c dims₀).supply
        apply PrivateReadCells.of_padded (bank g) c.header supply stage
        · exact view.hdr.native 3
        · have issuedZero:=ShrinkOutput.selected_padding B.shrink s D rem hD small A cur before c branch H
            oldCap baseRoom wide icRoom offset v g (Nat.le_of_not_gt live) (⟨1,by decide⟩ : Fin 6)
          have lower : hdr≤rowAddr g.val+1 := (range g (1 : Fin 6)).1
          have upper : rowAddr g.val+1<(en c).next.heap := (range g (1 : Fin 6)).2
          rw [wordAt,incident g.val state,←Nat.cast_add,Fin.val_cast_of_lt (upper.trans endRoom),
            high state _ (area.trans lower),arrayHi _ lower upper]
          simpa only [rowAddr,Nat.add_assoc,Fin.val_mk] using issuedZero.2
        · intro j
          have hh:=H.cursor.earlier
          have jj:=j.isLt
          exact ⟨by omega,by omega⟩
        · intro j
          let : Nonempty (X).Base:=⟨v.1⟩
          have positive : 0<(dims₀).motifs := by
            simp only [Dimensions.motifs,Dimensions.upperBlocks,Dimensions.oldEdges,dims,shrinkStage]
            positivity
          obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩:=H.cursor.allocated
          have last:=H.cursor.end_lt
          have jlt:=j.isLt
          dsimp only [supply]
          exact ⟨by omega,by omega⟩
  have queries (k : Fin (f).motifs) (group : Bool) (μ : Memory W) (state : seen μ) :
      let G:=withMotif J k.val
      Protected (joinHeader G W group) μ (G.party.seed+64) (HistoryMotifJoin.rows G W group).length ∧
      (HistoryNodePorts.id G.nodePorts).value (fun _=>0) μ (fun _=>0)=(node:Word W) ∧
      (selected G μ).oldBits+(selected G μ).newBits=(p:Word W) ∧
      wordAt μ (selected G μ).kernel 3=(count:Word W) :=
    ⟨joinHeader_physical (banks.withMotif k.val) age vbig group node nr stat (by change 0<(6:ℕ);decide)
      (fun _=>k.isLt) (nodeReads state) (motifReads k state) (getId state)
      ((childNum state).le.trans ((Nat.le_succ _).trans capRoom)),
      getId state,portFit state,by
        simpa only [Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.val_succ,Fin.val_zero] using
          kw k.val state (0 : Fin 2).succ.succ.succ⟩
  have emptyRoom (g : Fin (f).motifs) (j : Fin 6) (m : Memory W) (resident : seen m)
      (off : ∀ h:g.val<count,partySite P lay (order.equiv ⟨g.val,h⟩).val j≠v) :
      VacantRoom (withParty (bank g) j.val) node encode m := by
    have high (a : ℕ) (ha : base u 19≤a) := resident.retained a (outside_of_region node age nr (.inr (.inl ha)))
    have current : numeric m (base u 18)-1=node:=by
      rw [numeric,resident.retained _ (outside_of_region node age nr (.inr (.inr (.inl rfl))))]
      exact cursor
    have kn:=high (base u 44+8*node+5) (by have:=apart (u:=u) (by decide : 19<44);omega)
    have six : 2^(f).parties<2^W:=by change 2^6<2^W;exact Nat.pow_lt_pow_right (by decide) (by omega)
    have lo : base u 18≤hdr:=by have:=apart (u:=u) (by decide : 18<19);omega
    exact (recorded_vacant_room B s D rem hD small A u arch f node cur ctr before issued final m c branch
      hdr H saved v order g.val j oldCap baseRoom wide icRoom offset guard
      (fun a l h=>(high a (area.trans l)).trans (oldArchive a l h)) kmin rmin lo current
      (kn.trans original) rfl off encode age nr g.isLt stat six lookup lutStride pageStart pageStride counts
      (.inr lutAway) (.inr countsAway) headSize portRoom).1
  have single (i : Fin count) : 4*(piece (row i)).resources≤V₁:=by
    let trees:=Children.join 0 count (fun _=>p) (fun _ j=>.pin j) (fun i=>piece (row i))
    exact (Nat.mul_le_mul_left 4 (trees.factor_resources_le i)).trans size
  have partyRead {g k : ℕ} {μ : Memory W} (state : seen μ) (Z : SiteSlot F W p (withMotif J g))
      (held : Z.prefixWords (u:=u) node encode μ k) :
      ArmRead u node cap (withMotif J g) input μ (Z.arms.entry node encode (Z.init μ) k) :=
    SiteRead.at_party (B:=B) (level:=level) (u:=u) (start:=start) (height:=height) (K:=K)
      (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt)
      (previous:=previous) (successor:=successor) (v:=v) (node:=node) (input:=input)
      (k:=g) (partyIndex:=k) μ state Z age capRoom held
  have occupied (i : Fin count) (state : seen (atSlot i.val)) :
      (slot i (atSlot i.val)).Live node encode (atSlot i.val) ∧
      (slot i (atSlot i.val)).ArmSpace node encode (atSlot i.val) u ∧ paidAt i (atSlot i.val) := by
    as_aux_lemma =>
      let g : Fin (f).motifs:=i.castLE available
      let startM:=atSlot i.val
      let Z:=slot i startM
      let m (k : ℕ):=Z.arms.entry node encode (Z.init startM) k
      have inside {k} (h : Z.prefixWords (u:=u) node encode startM k) :=
        partyRead (g:=i.val) state Z h
      apply issuedSlot_live encode (cloud i) (active i) (bundle i).arity (nets i) (bundle i).wire
        (rate i) startM (banks.withMotif i.val) nr stat g.isLt headSize privRoom (marked g startM state)
      · intro j h
        exact elected i j startM _ state (inside h) (shared i startM state)
      · intro j notHere words
        exact emptyRoom g j (m j.val) (inside words).toSiteRead (fun _=>notHere)
      · intro words
        let μ : Memory W := m 6
        have now : ArmRead u node cap (cloud i) input startM μ := inside (k:=6) words
        have resident : seen μ := now.toSiteRead
        have joinReads := queries g true μ resident
        have partyOrder := mask i μ resident
        have total := occupied_private_total (A:=cloud i) (m:=startM) (after:=μ)
          (shared i startM state) (indices i) privRoom (now.privatePrefix ⟨8,by decide⟩)
        exact Children.finish_chart (u:=u) (node:=node) (A:=cloud i) (bundle i).native Z.arms μ encode
          (banks.withMotif i.val) age nr stat g.isLt rfl (single i) pins tags
          joinReads.1 joinReads.2.1 joinReads.2.2.1 total partyOrder.1 partyOrder.2
  have padded (g : Fin (f).motifs) (off : count≤g.val) (state : seen (atSlot g.val)) :
      let Z:=emptySlot (F:=F) («W»:=W) («p»:=p) (bank g)
      Z.Live node encode (atSlot g.val) ∧ Z.ArmSpace node encode (atSlot g.val) u := by
    as_aux_lemma =>
      let startM:=atSlot g.val
      let Z:=emptySlot (F:=F) («W»:=W) («p»:=p) (bank g)
      let m (k : ℕ):=Z.arms.entry node encode (Z.init startM) k
      have inside {k} (h : Z.prefixWords (u:=u) node encode startM k) :=
        partyRead (g:=g.val) state Z h
      have gFits : g.val<2^W:=g.isLt.trans icRoom
      have cFits : count<2^W:=available.trans_lt icRoom
      have inactive {μ : Memory W} (hold : seen μ) :
          ¬((bank g).party.motif:Word W)<wordAt μ (selected (bank g) μ).kernel 3:=by
        rw [(queries g true μ hold).2.2.2]
        change ¬(((g.val:ℕ):Word W)).val<((count:Word W)).val
        rw [Fin.val_cast_of_lt gFits,Fin.val_cast_of_lt cFits]
        omega
      apply Z.issued_live node encode startM (banks.withMotif g.val) nr stat g.isLt headSize
        privRoom (marked g startM state)
      · intro j words
        refine ⟨⟨headSize,fun i=>Fin.elim0 i,fun i=>Fin.elim0 i,fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩,
          fun _=>emptyRoom g j (m j.val) (inside words).toSiteRead (fun h=>False.elim (by omega)),
          fun i=>Fin.elim0 i⟩
      · intro words
        have now:=inside words
        obtain ⟨safe,atN,ports,_⟩:=queries g true (m 6) now.toSiteRead
        exact emptySlot_chart startM (m 6) encode (banks.withMotif g.val) age nr stat g.isLt rfl
          pins safe atN ports (inactive state) (inactive now.toSiteRead) privRoom (now.privatePrefix 8)
  exact assemble_recorded_site B level u start height K rem hD small A branch gt
    previous successor v order node input age nr capRoom available stat size pins tags
    (by exact @startRun) occupied padded queries

/-- The charge of an empty physical party includes both native initializers. -/
private theorem vacant_grid_cost {F : Type} (G : Grid F) (L : HistoryGatherBody.Layout)
    {w₀ : ℕ} (m : Memory w₀) (r : ℕ) (same : Same L (kernelTemplate G)) :
    vacantPairCost L m+vacantMapCost L w₀ ≤
      (gridPairRate G+gridMapRate G)*((w₀+1)^3*(1+r)) := by
  let units:=(w₀+1)^3*(1+r)
  have positive : 0<units := by dsimp only [units];positivity
  have room : (w₀+1)^3 ≤ units :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h : vacantPairCost L m≤partyTariff 0 0 0 0 0*(w₀+1)^3 := by
    simpa only [vacantPairCost,Nat.add_zero,Nat.mul_one] using (vacant_pair_tariff L.party m 0 0 0 0 0)
  have pairRate : partyTariff 0 0 0 0 0≤gridPairRate G := Nat.le_add_right _ _
  have mapRate : HistoryGatherExecution.schemaCost (kernelTemplate G)≤gridMapRate G := Nat.le_add_right _ _
  rw [Nat.add_mul]
  exact Nat.add_le_add (h.trans (Nat.mul_le_mul pairRate room))
    ((vacant_map_ticks L (kernelTemplate G) same).trans
      (mapRate.trans (Nat.le_mul_of_pos_right _ positive)))

set_option maxRecDepth 18000 in
set_option maxHeartbeats 2400000 in
/-- Price the real public roster, including unused incidences. Each achieved
pair and its gather share the allowance for their single elected party. -/
theorem recorded_site_cost (available : count≤(J).party.motifs)
    (paid : ∀ i : Fin count,paidAt i (atSlot i.val)) :
    (run).cost node encode first compiled (HistoryNodePorts.phaseCost cap) ≤
      blockKernelRate B*((W+1)^3*(1+∑ i : Fin count,many (row i))+1+(siteTree).resources) := by
  let G:=shrinkGrid B level
  let pair:=gridPairRate G
  let gather:=gridMapRate G
  have page : G ∈ grids B := by
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨level,rfl⟩
  have same : Same J reference := ⟨rfl,rfl,rfl,rfl,rfl⟩
  apply shrink_block_ticks B G page J same node (atSlot (J).party.motifs) encode
    (partySite P lay) v order.equiv (fun z=>piece z.val) (fun z=>many z.val)
    ((run).slotCost node encode first) available
  intro k hk
  let L:=withMotif J k
  have localSame : Same L reference := ⟨rfl,rfl,rfl,rfl,rfl⟩
  let m:=atSlot k
  by_cases found : k<count
  · let i : Fin count:=⟨k,found⟩
    let C:=bundle i
    let Z:=slot i m
    let ar:=issuedRows i m
    let incoming:=Z.init m
    let after:=ar.entry node encode incoming L.party.parties
    have six : L.party.parties = 6 := rfl
    have size : recordedRoleCount (active i) ≤ L.party.parties :=
      (recordedRoleCount_le_six (active i)).trans_eq six.symm
    let r:=many (row i)
    have joint (j : ℕ) (_hj : j<L.party.parties) :
        ar.ticks node encode incoming j+ar.mapTicks j≤(pair+gather)*((W+1)^3*(1+r)) := by
      cases onRole : ar.select j with
      | none =>
        simp only [ArmRows.ticks,ArmRows.mapTicks,onRole]
        exact vacant_grid_cost G (withParty L j) _ r ⟨rfl,rfl,rfl,rfl,rfl⟩
      | some a =>
        have key : ((roles i) a).val.val=j := maskSelect_some L (active i) onRole
        have jointPaid:=paid i a
        rw [key] at jointPaid
        simp only [ArmRows.ticks,ArmRows.mapTicks,onRole]
        apply jointPaid.trans
        have fees:=party_rates_in_grid G (party i a) (grid_has (shrinkParty B.shrink) _ _)
        change partyRate (party i a)*(W+1)^3*(1+r)+partyMapRate reference (party i a)*(1+r)≤_
        rw [Nat.add_mul,Nat.mul_assoc]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ fees.1)
          (Nat.mul_le_mul fees.2 (Nat.le_mul_of_pos_left _ (by positivity)))
    have final:=emit_motif_ticks L reference localSame node after C.factor C.wire encode size r pair gather
      (ar.ticks node encode incoming) ar.mapTicks joint
    simp only [dite_eq_left found]
    change ((run).slot i.val m).cost node encode m≤_
    rw [recordedSite_occupied]
    calc
      _ ≤ _ := final
      _ = _ := congrArg (fun T=>motifRate reference pair gather*((W+1)^3*(1+r)+T.resources)) C.eqn.symm
  · let Z:=emptySlot (F:=F) («W»:=W) («p»:=p) L
    let ar:=Z.arms
    let incoming:=Z.init m
    let after:=ar.entry node encode incoming L.party.parties
    let emptyFactors : ∀ i : Fin 0,Tree F (Fin.elim0 i) := fun i => Fin.elim0 i
    let wire : ∀ i : Fin 0,Fin (Fin.elim0 i)→BitSource 0 p := fun i => Fin.elim0 i
    have joint (j : ℕ) (_hj : j<L.party.parties) :
        ar.ticks node encode incoming j+ar.mapTicks j≤(pair+gather)*((W+1)^3*(1+0)) :=
      vacant_grid_cost G (withParty L j) _ 0 ⟨rfl,rfl,rfl,rfl,rfl⟩
    have final:=emit_motif_ticks L reference localSame node after emptyFactors wire encode (Nat.zero_le _) 0
      pair gather (ar.ticks node encode incoming) ar.mapTicks joint
    have res : (Tree.join 0 0 Fin.elim0 wire emptyFactors).resources=1 := by
      simp [Tree.resources,Stage.treeWork,Tree.bits,Tree.rows,Tree.nodes,Tree.footprint]
    rw [res] at final
    simp only [dite_eq_right found]
    change ((run).slot k m).cost node encode m≤_
    rw [recordedSite_padding (after:=Nat.le_of_not_gt found)]
    exact final


/-- The cached output of a shrink kernel, in the two banks used by the
following node join. The four info words describe the very same typed root. -/
def Emitted (root : Σ n,Tree F n) (totalCopies : ℕ) (post : Memory W) (ticks : ℕ) : Prop :=
  (kernelProcedure J W cap).Exec input post ticks ∧
  HistoryCompiledRows.Records encode root.2.compile (kernelBase u node f 0) post ∧
  (∀ j : Fin 4,post (kernelBase u node f 1+j.val)=
    ((HistoryBoundedJoin.Info.mk (kernelBase u node f 0) root.1 root.2.rows root.2.bits).words j:Word W)) ∧
  (∀ a,OutsideNode u node a→post a=input a) ∧
  ticks≤blockKernelRate B*((W+1)^3*(1+totalCopies)+1+root.2.resources)

variable (words : A.Words Pins)
local notation "past" => (StageAddress.shrinkInputIso (X).graph (X).chart (shrinkRecordLane s rem)
  P rfl (X).width).pushWord (A.laneWords (rootLaneEq s rem) words)
open private branchFintype from OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
local notation "nextWord" => shrinkWordLayout (F:=F) (Pins:=Pins) (V:=(X).Base)
  (H:=BitWord s) (Tag:=BitWord t) (L:=BitWord rem) («d»:=d) (c:=2*d+1) P baseWidth many entries
  (@Fintype.equivFin (shrinkRecordHists B.shrink s rem A)
    (branchFintype B.shrink X (shrinkRecordLane s rem) P (Nat.two_pow_pos s) (shrinkRecordCode s rem A))).symm
  binary_neg valid (S).pieces edgeOrd hc pad extra
  (branch.cast (shrinkBinary_ruleCount B.shrink s D rem hD small A))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
omit [Fintype F] in
/-- The successor word chart uses exactly the stored outgoing and incoming slots. -/
theorem recorded_successor_order :
    ∃ h : (nextWord).count v=2*(Graph.liveDegree S+pad),
      ∀ k, (nextWord).order v k=HalfOrder.order Gnew v (k.cast h) :=
  ⟨rfl,fun _=>rfl⟩

local notation "oldPinAt" site:arg => WordLayout.oldPin past nextWord ((P).placement lay) children childOrder site
local notation "newPinAt" site:arg => WordLayout.newPin past nextWord ((P).placement lay) children childOrder site
local notation "actualWidth" => WordLayout.argSize past nextWord ((P).placement lay) children childOrder v

set_option maxRecDepth 22000 in
set_option maxHeartbeats 3000000 in
private def recordedWordChildren (targetSite : Computability.VPVNP.Compression.Site (X).Base (BitWord t) (BitWord rem))
    (motifKey : (P).Motif) :=
  tariffPieceChildren (F:=F) («p»:=WordLayout.argSize past nextWord ((P).placement lay) children childOrder targetSite) P oldWidth₀ rawCode (selected_bundle_positive s) numbers
    baseWidth many entries hist binary_neg valid (S).pieces (copiesPositive s D hD small) edgeOrd hc pad extra
    targetSite lay (oldPinAt targetSite) (newPinAt targetSite) motifKey

local notation "wordChildrenAt" site:arg motif:arg => recordedWordChildren (B:=B) (level:=level) (rem:=rem)
  (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt) (words:=words) site motif
local notation "actualBundle" i:arg => wordChildrenAt v (row i)
local notation "actualNets" i:arg => fun j=>((actualBundle i).factor j).compile
local notation "actualTree" => shrinkSite P oldWidth₀ rawCode (selected_bundle_positive s) numbers
  baseWidth many entries hist binary_neg valid (S).pieces (copiesPositive s D hD small) edgeOrd hc pad extra
  v (oldPinAt v) (newPinAt v) order.equiv
local notation "wordStep" => shrinkBinary_assembler B.shrink s D rem hD small A words branch

set_option maxRecDepth 22000 in
set_option maxHeartbeats 3000000 in
/-- Native reads and bounded writes produced at the currently elected raw party. -/
def OccupiedWrites : Prop :=
  ∀ (i : Fin count) (j : Fin (recordedRoleCount (active i))) (startM now : Memory W),seen startM →
      ArmRead u node cap (cloud i) input startM now→
      PrivateSite (geo:=S) (cloud i) startM (owns i) (widths i)→
      ∃ w,ArmWrite.Real u node encode (maps i j) (((wordChildrenAt v (row i)).factor j).compile)
        ((wordChildrenAt v (row i)).wire j) now w ∧
        w.ticks+HistoryGatherExecution.tariff W (maps i j) w.plan≤rate i j

private theorem selectedAlphabetBound {α β : Type*} (order : α ≃ β) (size : α → ℕ)
    (bound : ℕ) (fits : ∀ k, size (order.symm k) ≤ bound) (m : α) : size m ≤ bound :=
  (congrArg (fun a => size a ≤ bound) (order.symm_apply_apply m)).mp (fits (order m))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4800000 in
/-- Every occupied arm of this chronological root uses the accepted tile and
its own two saved half-edge tables. The copy quota is the price of this node. -/
theorem recorded_occupied_arms (cur ctr : Word W) (before issued final : Memory W) (c : Cursor) (head : ℕ)
    (H:ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved:SavedFrame cur ctr head (en c).next.header (en c).next.heap issued final)
    (caps:ShrinkNativeCaps B.shrink s D rem W A) (bounds:RecordedArrayBounds W head c A)
    (control:cur.val<ctr.val)
    (keep:∀a,(c.header≤a ∧ a<c.header+64 ∨ head≤a)→a<(en c).next.heap→input a=final a)
    (area:base u 19≤head) (current:numeric input (base u 18)=node+1)
    (original:input (base u 44+8*node+5)=((fields₀ c 34+5*siteNo:ℕ):Word W))
    (age:16≤u) (nr:node<V₁^2) (intrinsic:blockPageRate B≤u)
    (lib:Mounted B height W start input) (romHigh:base u 19 ≤ start) (romFit:start+libraryWords B height<2^W)
    (Kpos:0<K) (Kfit:K<2^W) (heightRoom:W≤height)
    (priorSites:(X).ArchiveSites) (ordered:(X).OrderedHalves (A.laneWords (rootLaneEq s rem) words))
    (oldRows:State.HalfRows priorSites (fun a=>base u 19≤a ∧ a<2^W) (numeric input))
    (directory:∀z,base u 44+(8*priorSites.id z+6)<2^W ∧
      numeric input (base u 44+(8*priorSites.id z+6))=priorSites.layer.incident+(priorSites.ord z).val*2)
    (T₀:HistoryStageRoot.Input) (nodeId:T₀.id=node) (nodeBase:T₀.nodeBase=base u 44) (cacheBase:T₀.resultBase=base u 13)
    (degree₀:HistoryStageRoot.childCount T₀ (numeric input)=siteCopies₀)
    (cached:∀k:Fin siteCopies₀,HistoryStageRoot.oldHalf (HistoryStageRoot.atResult (numeric input)
      (HistoryStageRoot.childPtr T₀ (numeric input) k.val))=(past).ports.halfBits (childOrder v k).val)
    (newBits:HistoryStageRoot.halfWidth T₀ (numeric input)=(nextWord).ports.halfBits v)
    (headAt:numeric input (HistoryStageRoot.node T₀+6)=halfHead₀ c)
    (childPtr:ℕ) (childTable:numeric input (HistoryStageRoot.node T₀+3)=childPtr)
    (arr:base u 19≤childPtr ∧ childPtr+siteCopies₀≤2^W)
    (childIds:∀k:Fin siteCopies₀,numeric input (childPtr+k.val)=priorSites.id ((inputChart₀).site.symm ((childOrder v k).val)))
    (siteSize:4*(actualTree).resources≤V₁) (pinRoom:actualWidth<2^W)
    (price:ℕ) (copies:∀i:Fin count,many (row i)≤price)
    (margin:gridPageRate (arity B) (shrinkGrid B level)*((price+1)*(W+1)^3)≤V₁) :
    OccupiedWrites (B:=B) (level:=level) (u:=u) (start:=start) (height:=height) (K:=K) (rem:=rem)
      (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt) (words:=words)
      (v:=v) (order:=order) (node:=node) (input:=input) := by
  let gr:=shrinkGrid B level
  have inGrid : gr∈grids B:=List.mem_append_left _ (List.mem_ofFn.mpr ⟨level,rfl⟩)
  have rateBound:=(grid_page_rate_le_block B inGrid).trans intrinsic
  have uw:u≤u^10:=Nat.le_self_pow (by decide) u
  have seq:u<V₁:=uw.trans_lt Nat.lt_two_pow_self
  have wide:8≤W:=by omega
  have large:V₁<2^W:=Nat.pow_lt_pow_right (by decide) (by omega)
  have vpos:128≤V₁:=by change 2^7≤2^(u^10);exact Nat.pow_le_pow_right (by decide) (by omega)
  have stat:((f).motifs+2)*((f).parties+2)*8*32≤V₁:=by
    change (gr.motifs+2)*(gr.parties+2)*8*32≤V₁
    unfold gridPageRate at rateBound;omega
  have headSize:3+5*(f).demands+4*(f).supplies≤V₁:=by
    change 3+5*gr.demand+4*gr.supply≤V₁;unfold gridPageRate at rateBound;omega
  have capRoom:cap+1≤V₁:=by
    have nn:0<(f).parties+2:=by omega
    have q:=Nat.le_mul_of_pos_right ((f).motifs+2) nn
    have hd:d≤8*d^2:=by have:=Nat.le_self_pow (by decide:2≠0) d;omega
    have h:=Nat.mul_le_mul_right (2^(2*d+1)) hd
    change d*2^(2*d+1)+1≤V₁
    change 8*d^2*2^(2*d+1)+2≤_ at q
    omega
  have safe:=H.cursor.controls.trans_lt cur.isLt
  have next:=NavigationDirectory.heap_step K c (.shrink dims₀)
  have afterHeap:head≤c.heap:=bounds.graphLow.trans ((Nat.le_add_right _ _).trans H.cursor.graph)
  have moves:=descriptorAllocation K c (.shrink dims₀)
  have lowK:c.heap≤fields₀ c 34:=moves.1
  have lowR:c.heap≤fields₀ c 36:=moves.2.2.1
  have guard (a:ℕ) (_:head≤a) (hi:a<(en c).next.heap) : a≠cur.val ∧ a≠ctr.val:=
    ⟨(hi.trans_le H.cursor.controls).ne,((hi.trans_le H.cursor.controls).trans control).ne⟩
  have headerRead (a:ℕ) (lo:c.header≤a) (hi:a<c.header+34) : input a=issued a:=by
    have under:a<(en c).next.heap:=by have:=H.cursor.earlier;omega
    have h₁:=under.trans_le H.cursor.controls
    have headerLimit : a < (en c).next.header := by change a < c.header+64; omega
    exact (keep a (.inl ⟨lo,by omega⟩) under).trans (saved a h₁.ne (h₁.trans control).ne (.inl headerLimit) under)
  have countBound:=H.cursor.counts
  let Q:=shrinkBinaryFamily B.shrink s D rem hD small A
  have wholeFront : c.dense+K*Q.motifs≤c.heap:=countBound
  have live (i:Fin Q.motifs) : c.dense+i.val*K+K≤c.heap:=by
    have h:=Nat.mul_le_mul_left K (Nat.succ_le_iff.mpr i.isLt)
    rw [Nat.mul_succ,Nat.mul_comm K i.val] at h
    omega
  have dense (i:Fin Q.motifs) (a:Q.alphabet i) :
      let addr:=c.dense+i.val*K+(Fintype.equivFin _ a).val
      addr≠c.header+27 ∧ head≤addr ∧ addr<(en c).next.heap := by
    have inside:=(Fintype.equivFin _ a).isLt.trans_le (H.registerFit.1 i)
    have:=bounds.headerDense;have:=bounds.denseLow;have:=live i
    dsimp only;omega
  have available:count≤(f).motifs:=(ShrinkOutput.selected_kernel B.shrink s D rem hD small A cur before c branch H
    caps.1 caps.2.1 wide caps.2.2 bounds.widthPos v 0).2.2
  have childCap:siteCopies₀≤cap:=le_rfl
  have space:base u 18+V₁^4<2^W:=TickWorkspace.word_space (u:=u) (i:=18) (by omega) (by
    change 18 < V₁^4
    have:=Nat.le_self_pow (by decide:4≠0) V₁;omega)
  have prefixRoom:(J).nodePorts.starts+siteCopies₀<2^W ∧ (J).privateStarts+9<2^W:=by
    change base u 18+3*V₁+siteCopies₀<2^W ∧ base u 18+4*V₁+9<2^W
    have sq:32*V₁≤V₁^2:=by rw [pow_two];exact Nat.mul_le_mul_right V₁ (by omega)
    have quart:=Nat.pow_le_pow_right (by omega:0<V₁) (by decide:2≤4)
    omega
  have highCounts:=area.trans bounds.denseLow
  intro i j startM now _ reads priv
  let ix:=shrinkRecordOrder s rem A (row i)
  let n:=Fintype.card (entries (row i)).Alphabet
  have letters : n ≤ K := selectedAlphabetBound (shrinkRecordOrder s rem A)
    (fun m => Fintype.card (entries m).Alphabet) K H.registerFit.1 (row i)
  have countWin:archiveWindow u (c.dense+ix.val*K) ((party i j).kind (arity B)).letters:=by
    have chosen : B.shrink.row (tileNo i) =
        PhysicalShrink.picked B.shrink P oldWidth₀ (shrinkRecordCode s rem A) hc (row i) :=
      B.shrink.row_chosen _
    have letterCount : ((party i j).kind (arity B)).letters=n :=
      congrArg (fun r => Fintype.card (B.shrink.block r).Alphabet) chosen
    have heapBound : c.heap ≤ (en c).next.heap :=
      (Nat.le_add_right c.heap _).trans_eq next.symm
    have countsEnd := (Nat.add_le_add_left (letterCount.le.trans letters) (c.dense+ix.val*K)).trans (live ix)
    have above : base u 18 ≤ base u 19 :=
      (Nat.le_add_right _ _).trans (TickWorkspace.apart (u:=u) (by decide : 18 < 19))
    exact ⟨countsEnd.trans_lt (heapBound.trans_lt safe),
      .inr ((above.trans highCounts).trans (Nat.le_add_right _ _))⟩
  let top:=shrinkMotifWidthFactor B.shrink (2*d+1) d*(1+A.maxWidth)
  have each:=shrink_issued_room B.shrink s D rem hD small A branch
  have score:=caps.score
  have one:0<Fintype.card (P).Motif:=Fintype.card_pos_iff.mpr ⟨row i⟩
  have widthRoom:(∑e:Fin 8,(widths i) e)<2^W:=by
    have h:(∑e:Fin 8,(widths i) e)≤∑_ : Fin 8,top:=Finset.sum_le_sum (fun e _=>each _ e)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
    change 80*Fintype.card (P).Motif*top^2<2^W at score
    have h₂:=Nat.le_mul_of_pos_left (top^2) (show 0<80*Fintype.card (P).Motif by omega)
    have h₃:=Nat.le_mul_of_pos_right (80:ℕ) one
    have h₄:=Nat.mul_le_mul_right (top^2) h₃
    by_cases z:top=0
    · rw [z] at h;omega
    · nlinarith [Nat.le_self_pow (by decide:2≠0) top]
  have deg:2*D<2^W:=caps.halfCount
  exact recorded_positive_arm (B:=B) (level:=level) (u:=u) (start:=start) (height:=height) (K:=K)
    (rem:=rem) (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt)
    (previous:=past) (successor:=nextWord) (v:=v) (order:=order) (node:=node) (input:=input)
    (cur:=cur) (ctr:=ctr) (before:=before) (issued:=issued) (final:=final) (c:=c) (hdr:=head) H saved
    caps.1 caps.2.1 wide caps.2.2 bounds.widthPos guard (fun a lo hi=>keep a (.inr lo) hi)
    (afterHeap.trans lowK) (afterHeap.trans lowR) area (by rw [current];omega) original caps
    bounds.toOldArrayBounds bounds.header_at headerRead age nr available stat headSize capRoom lib
    ⟨romFit,.inr (by have:=TickWorkspace.apart (u:=u) (by decide:18<19);omega)⟩
    romHigh Kpos Kfit dense i j startM now reads (A.laneWords (rootLaneEq s rem) words) ordered rfl
    priorSites T₀ nodeId nodeBase cacheBase rfl (fun _=>rfl) degree₀ cached newBits headAt afterHeap
    childCap prefixRoom.1 pinRoom prefixRoom.2 oldRows directory childPtr childTable arr childIds deg priv widthRoom
    siteSize heightRoom price (copies i) margin countWin highCounts (block_tags_at_age B intrinsic)

open private lanes_eq from OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily

private theorem recorded_compiled_dimensions {coefficient : Type*} {pinCount limit : ℕ}
    {tree : Tree coefficient pinCount} (_room : 4 * tree.resources ≤ limit) :
    tree.compile.cells = tree.rows ∧ tree.compile.internal = tree.bits :=
  ⟨Tree.compiled_rows tree, Tree.compiled_bits tree⟩

private theorem emitted_info_transport {w : ℕ} {m : Memory w}
    {fromAddr toAddr fromStream toStream fromPins toPins fromRows toRows fromBits toBits : ℕ}
    (incoming : ∀ j : Fin 4, m (fromAddr+j.val) =
      ((HistoryBoundedJoin.Info.mk fromStream fromPins fromRows fromBits).words j : Word w))
    (addr_eq : fromAddr = toAddr) (stream_eq : fromStream = toStream)
    (pins_eq : fromPins = toPins) (rows_eq : fromRows = toRows) (bits_eq : fromBits = toBits) :
    ∀ j : Fin 4, m (toAddr+j.val) =
      ((HistoryBoundedJoin.Info.mk toStream toPins toRows toBits).words j : Word w) := by
  cases addr_eq
  cases stream_eq
  cases pins_eq
  cases rows_eq
  cases bits_eq
  exact incoming

set_option maxRecDepth 22000 in
set_option maxHeartbeats 3000000 in
/-- Run the physical shrink procedure for this exact chronological word.
The old geometry supplies the numerical root order, and all pair and gather
charges are accounted for by the elected arms of the archived roster. -/
theorem emit_recorded_shrink (cur ctr : Word W) (before issued final : Memory W) (c : Cursor) (hdr : ℕ)
    (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved : SavedFrame cur ctr hdr (en c).next.header (en c).next.heap issued final)
    (caps : ShrinkNativeCaps B.shrink s D rem W A) (rawArrays : RecordedArrayBounds W hdr c A)
    (controlsApart : cur.val<ctr.val)
    (headerOld : ∀a,c.header≤a→a<c.header+34→input a=final a)
    (strPos : 0<K) (strRoom : K<2^W)
    (oldArchive : ∀a,hdr≤a→a<(en c).next.heap→input a=final a)
    (area : base u 19≤hdr) (current : numeric input (base u 18)=node+1)
    (age : 16≤u) (nr : node<V₁^2) (intrinsic : blockPageRate B≤u)
    (romHigh : base u 19 ≤ start) (romFit : start+libraryWords B height<2^W)
    (pins : actualWidth<2^W)
    (size : 4*(actualTree).resources≤V₁)
    (z : ((M).next branch).Site)
    (halfBefore : State.HalfRows (shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch)
      (fun a=>base u 19≤a ∧ a<2^W) (numeric input))
    (atNode : let O:=shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch
      node=O.layer.first+(O.ord z).val ∧ (O.ord z).val=siteNo)
    (b : NavigationNodeRows.Banks) (nodeBase : b.nodes=base u 44)
    (dir : let O:=shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch
      HistoryStageSetup.DirectoryRow b O.layer (O.ord z) input)
    (data : NavigationNodeRows.LayerData (nodeLayer K c (.shrink dims₀)))
    (read : data.Reads (numeric input))
    (cells : data.Footprint (fun a=>base u 19≤a ∧ a<2^W) (numeric input))
    (childrenSmall : ∀ k, data.child
      ((shrinkArchiveSites (K:=K) B.shrink s D rem hD small A c branch).ord z) k<V₁^2)
    (totalPorts : childWidth (J).nodePorts cap (numeric input) ((J).nodePorts.starts+cap)+
      ((M).next branch).incidentWidth z=actualWidth)
    (elected : ∀ (i : Fin count) (j : Fin (recordedRoleCount (active i))) (startM now : Memory W),seen startM →
      ArmRead u node cap (cloud i) input startM now→
      PrivateSite (geo:=S) (cloud i) startM (owns i) (widths i)→
      ∃ w,ArmWrite.Real u node encode (maps i j) ((actualNets i) j) ((actualBundle i).wire j) now w ∧
        w.ticks+HistoryGatherExecution.tariff W (maps i j) w.plan≤rate i j) :
    ∃ post ticks,Emitted B level u start height K node input ((wordStep).rootPacket z)
      (∑ i : Fin count,many (row i)) post ticks := by
  have arrived : shrinkPackOrder s D rem A v=
      shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z) :=
    Fin.ext ((shrinkPackOrder_val s D rem A v).trans atNode.2.symm)
  have root : (wordStep).rootPacket z=(⟨actualWidth,actualTree⟩ : Σ n,Tree F n) :=
    shrink_word_root_at B.shrink s D rem hD small A words branch z v arrived order
      (ShrinkOutput.rootKeys B.shrink s D rem hD small A H)
  let laneLayout : (X).Words Pins := A.laneWords (lanes_eq s rem) words
  let inputWord := (StageAddress.shrinkInputIso (X).graph (X).chart (shrinkRecordLane s rem)
    P rfl (X).width).pushWord (G:=StageAddress.portGraph (X).graph (X).chart) (w:=(X).width)
      (H:=oldGraph P) (b:=shrinkRecordWidth s rem A) (Pins:=Pins) laneLayout
  let outputWord := nextWord
  have reached := recorded_site_exec (F:=F) (Pins:=Pins) (B:=B) (level:=level) (u:=u) (start:=start) (height:=height) (K:=K) (rem:=rem)
    (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt) (previous:=inputWord) (successor:=outputWord)
    (v:=v) (order:=order) (node:=node) (input:=input)
    cur ctr before issued final c hdr H saved caps
    rawArrays controlsApart headerOld strPos strRoom oldArchive area current age nr
    intrinsic romHigh romFit pins size z halfBefore atNode b nodeBase
    dir data read cells childrenSmall totalPorts elected
  have wordPositive : 0<u^10 := pow_pos (by omega : 0<u) _
  have available : count≤(J).party.motifs :=
    (ShrinkOutput.selected_kernel B.shrink s D rem hD small A cur before c branch H caps.1 caps.2.1
      (by omega : 8≤W) caps.2.2 rawArrays.widthPos v 0).2.2
  have charge := recorded_site_cost (F:=F) (Pins:=Pins) (B:=B) (level:=level) (u:=u) (start:=start) (height:=height) (K:=K) (rem:=rem)
    (hD:=hD) (small:=small) (A:=A) (branch:=branch) (gt:=gt) (previous:=inputWord) (successor:=outputWord)
    (v:=v) (order:=order) (node:=node) (input:=input)
    available reached.2.2.2.2
  have dimensions := recorded_compiled_dimensions size
  rw [root]
  refine ⟨_,_,reached.1,reached.2.1,?_,reached.2.2.2.1,charge⟩
  refine emitted_info_transport (reached.2.2.1) ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact dimensions.1
  · exact dimensions.2

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
