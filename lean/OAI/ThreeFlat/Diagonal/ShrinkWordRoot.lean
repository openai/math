import OAI.ThreeFlat.Diagonal.ShrinkChildAssemblyOrder

namespace OAI
/-! # The literal shrink kernel at the archived term and packed site -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking CompressorPacking.PhysicalShrink HistoryContraction
open Native Native.ShrinkStage Native.Placement Native.Graph NavigationPass ShrinkStageNav
open scoped Classical BigOperators
open private count_pos from OAI.ThreeFlat.Diagonal.PhysicalShrink
variable {F Pins : Type} [Field F]

def Move.WordStep.rootPacket {d l D m : ℕ} {A : State d l} {R : Move F A D m}
    {L : A.Words Pins} {i : Fin R.rules.count} (s : R.WordStep Pins L i) (v : (R.next i).Site) :
    Σ n,Tree F n :=
  ⟨_,s.stage.root (Move.WordStep.targetSite (R:=R) (i:=i) v)⟩

private def rootTest {d l D m : ℕ} {A : State d l} {R : Move F A D m} (J : R.Assembler Pins)
    (L : A.Words Pins) (test : ℕ→ℕ→(Σ n,Tree F n)→Prop) : Prop :=
  ∀ i v,test i.val (Halves.siteNumber (R.next i).order ((R.next i).chart.symm v)) ((J L i).rootPacket v)

private theorem root_degree {d l D D' m : ℕ} {A : State d l} (e : D=D') (R : Move F A D m)
    (J : R.Assembler Pins) (L : A.Words Pins) (test) (good : rootTest J L test) :
    rootTest (Move.castAssembler e R J) L test := by cases e; exact good

private theorem root_lane {d l l' D m : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D m) (J : R.Assembler Pins) (L : A.Words Pins) (test)
    (good : rootTest J (A.laneWords e L) test) : rootTest (Move.inputAssembler e A R J) L test := by
  cases e;exact good


section Raw
variable {d lanes h t rem D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset) (hd : 0<d) (hD : 0<D)
    (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D≤1/1024) (tagSize : 1<2^t)
    (code : Arc A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ)

private theorem rootColorCount (d : ℕ) (hd : 0<d) : 2≤2*d+1 := by omega

private abbrev rootLayout (i : Fin (Fintype.card (shrinkBranches T A u P hd code))) :=
  ShrinkMotif.chooseWidths (issued T P (oldWidth A u) code (rootColorCount d hd)
    ((Fintype.equivFin (shrinkBranches T A u P hd code)).symm i))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
/-- The old and new bit projections in this tree are those of the pushforward of the
specific incoming words. The target is an ordinary packed site and the digit is an
ordinary finite-indexed histogram. -/
def shrinkKernelEnumerated (L : A.Words Pins) (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
    (v : Computability.VPVNP.Compression.Site A.Base (BitWord t) (BitWord rem)) {q : ℕ}
    (enum : Fin q ≃ MotifKernel.Active (partySite P (rootLayout T A u P hd code i)) v) : Σ n,Tree F n := by
  let c := 2*d+1
  have hc : 2≤c := by dsimp [c]; omega
  let w := oldWidth A u
  let packed := (StageAddress.shrinkInputIso A.graph A.chart u P agree A.width).pushWord L
  let n := parallel c d D
  let pad := padding c d D
  let idle := tagPadding (V:=A.Base) (L:=BitWord rem) (Native.adjacentMask tagSize) (Native.adjacent_ne tagSize) pad
  let base := widths T P w code hc
  let many := r T P w code hc
  let tiles := tile T P w code hc
  let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm
  let lay := ShrinkMotif.chooseWidths (issued T P w code hc (hist i))
  let nchild := fun _ : Computability.VPVNP.Compression.Site A.Base (BitWord t) (BitWord rem)=>d*2^c
  let orderChild := fun v=>Owner.childOrder P lay v
  let positive := fun j=>(SlotEnergy.slotCount_mass (by positivity : 0<((2^c*d*d:ℕ):ℝ)/D) small j).1
  let next := shrinkWordLayout (Pins:=Pins) P base many tiles hist binary_neg good n order hc pad idle i
  exact ⟨_,shrinkSite P w code (count_pos hd hc) (motifNumbers P code hc) base many tiles (hist i)
    binary_neg good n positive order hc pad idle v (WordLayout.oldPin packed next (P.placement lay) nchild orderChild v)
    (WordLayout.newPin packed next (P.placement lay) nchild orderChild v) enum⟩

def shrinkKernel (L : A.Words Pins) (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
    (v : Computability.VPVNP.Compression.Site A.Base (BitWord t) (BitWord rem)) : Σ n,Tree F n :=
  shrinkKernelEnumerated T A u P agree good hd hD small tagSize code order L i v
    (Local.assemblyOrder P (rootLayout T A u P hd code i) v)

private theorem enum_eq {X Y : Type} (f : (q : ℕ) → (Fin q ≃ X) → Y) {a b : ℕ} (size : a=b)
    (first : Fin a ≃ X) (second : Fin b ≃ X) (agree : ∀i, first i=second (finCongr size i)) :
    f a first=f b second := by
  subst b
  have both : first=second := Equiv.ext (fun i=>by simpa using agree i)
  rw [both]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
private theorem raw_root (L : A.Words Pins) (test : ℕ→ℕ→(Σ n,Tree F n)→Prop)
    (accept : ∀ (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
      (v : Computability.VPVNP.Compression.Site A.Base (BitWord t) (BitWord rem)),test i.val (Incidents.siteNumber A.order v)
      (shrinkKernel T A u P agree good hd hD small tagSize code order L i v)) :
    rootTest (shrinkMove_assembler T A u P agree good hd hD small tagSize code order) L test := by
  unfold shrinkMove_assembler
  apply root_degree
  intro i v
  have ord : Halves.siteNumber (productOrder A.order (tagOrdinal t)) ((v.1,v.2.1),v.2.2)=
      Incidents.siteNumber A.order v := by
    simp [Halves.siteNumber,Incidents.siteNumber,productOrder,finProdFinEquiv_apply_val]; ring
  change test i.val (Halves.siteNumber (productOrder A.order (tagOrdinal t)) ((v.1,v.2.1),v.2.2)) _
  rw [ord]
  exact accept i v

end Raw

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
local notation "d" => (2^s:ℕ)
local notation "t" => CompressorPacking.tagBits (2^s)
local notation "S" => shrinkStage s D

theorem rootLaneEq : shrinkCharge s+rem=(2*d+1)+(s+(t+rem)) := by simp [shrinkCharge,Nat.add_assoc]

open private tag_size rawConditions from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor

private theorem tagsLarge : 1<2^t := tag_size s

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
def issuedRoot (L : A.Words Pins) (b : Fin (M).rules.count)
    (v : Computability.VPVNP.Compression.Site (B).Base (BitWord t) (BitWord rem)) : Σ n,Tree F n :=
  shrinkKernel T B (shrinkRecordLane s rem) P rfl (rawConditions s rem B)
    (Nat.two_pow_pos _) hD small (tagsLarge s) (shrinkRecordCode s rem A)
    (edgeOrder P (baseNat (B).order) (tagOrdinal t).toEmbedding (S).pieces (S).pieceRadix (shrinkPieceBound s D))
    (A.laneWords (rootLaneEq s rem) L) (b.cast (shrinkBinary_ruleCount T s D rem hD small A)) v

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The tree executed at one packed site using the emitted sequence of six-word incidence records. -/
def issuedRootAt {W : ℕ} (L : A.Words Pins) (b : Fin (M).rules.count)
    (v : Computability.VPVNP.Compression.Site (B).Base (BitWord t) (BitWord rem))
    (O : Incidents.SiteOrder («S» := shrinkStage s D) P (B).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords T s D rem hD small A b)) v W) : Σ n,Tree F n :=
  shrinkKernelEnumerated T B (shrinkRecordLane s rem) P rfl (rawConditions s rem B)
    (Nat.two_pow_pos _) hD small (tagsLarge s) (shrinkRecordCode s rem A)
    (edgeOrder P (baseNat (B).order) (tagOrdinal t).toEmbedding (S).pieces (S).pieceRadix (shrinkPieceBound s D))
    (A.laneWords (rootLaneEq s rem) L) (b.cast (shrinkBinary_ruleCount T s D rem hD small A)) v O.equiv

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
private theorem root_from_raw (L : A.Words Pins) (test : ℕ→ℕ→(Σ n,Tree F n)→Prop)
    (raw : rootTest (shrinkRaw_assembler T s D rem hD small B) (A.laneWords (rootLaneEq s rem) L) test) :
    rootTest (shrinkBinary_assembler T s D rem hD small A) L test := by
  unfold shrinkBinary_assembler
  apply root_lane
  exact raw

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem shrink_word_root (L : A.Words Pins) (b : Fin (M).rules.count) (v : ((M).next b).Site) :
    (shrinkBinary_assembler T s D rem hD small A L b).rootPacket v=
      issuedRoot T s D rem hD small A L b ((shrinkPackOrder s D rem A).symm
        (shrinkNextOrder T s D rem hD small A b (((M).next b).chart.symm v))) := by
  let observed (i j : ℕ) (x : Σ n,Tree F n) :=
    ∀ (branch : Fin (M).rules.count) (z : Computability.VPVNP.Compression.Site (B).Base (BitWord t) (BitWord rem)),
      i=branch.val → j=Incidents.siteNumber (B).order z → x=issuedRoot T s D rem hD small A L branch z
  have all : rootTest (shrinkBinary_assembler T s D rem hD small A) L observed := by
    apply root_from_raw
    unfold shrinkRaw_assembler
    apply raw_root
    intro idx site
    dsimp only [observed]
    intro branch z hidx hz
    have e : site=z := (shrinkPackOrder s D rem A).injective (Fin.ext
      ((shrinkPackOrder_val s D rem A site).trans (hz.trans (shrinkPackOrder_val s D rem A z).symm)))
    have i : idx=branch.cast (shrinkBinary_ruleCount T s D rem hD small A) := Fin.ext hidx
    subst idx;subst z
    rfl
  apply all b v b _ rfl
  rw [←shrinkNextOrder_val,←shrinkPackOrder_val,Equiv.apply_symm_apply]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem shrink_word_root_at {W : ℕ} (L : A.Words Pins) (b : Fin (M).rules.count)
    (v : ((M).next b).Site) (z : Computability.VPVNP.Compression.Site (B).Base (BitWord t) (BitWord rem))
    (site : (shrinkPackOrder s D rem A) z =
      shrinkNextOrder T s D rem hD small A b (((M).next b).chart.symm v))
    (O : Incidents.SiteOrder («S»:=S) P (B).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords T s D rem hD small A b)) z W)
    (fit : ∀ a, Demand.key P (baseNat (B).order) a+1<2^W) :
    (shrinkBinary_assembler T s D rem hD small A L b).rootPacket v =
      issuedRootAt T s D rem hD small A L b z O := by
  rw [shrink_word_root,←site,Equiv.symm_apply_apply]
  let lay:=ShrinkMotif.chooseWidths (shrinkIssuedWords T s D rem hD small A b)
  let idx:=b.cast (shrinkBinary_ruleCount T s D rem hD small A)
  let evaluate (q : ℕ) (e : Fin q ≃ MotifKernel.Active (partySite P lay) z) :=
    shrinkKernelEnumerated T B (shrinkRecordLane s rem) P rfl (rawConditions s rem B)
      (Nat.two_pow_pos _) hD small (tagsLarge s) (shrinkRecordCode s rem A)
      (edgeOrder P (baseNat (B).order) (tagOrdinal t).toEmbedding (S).pieces (S).pieceRadix (shrinkPieceBound s D))
      (A.laneWords (rootLaneEq s rem) L) idx z e
  change evaluate _ (Local.assemblyOrder P lay z) = evaluate _ O.equiv
  exact (enum_eq evaluate (Incidents.assembly_length («S»:=S) (w:=W) P (B).order lay z fit)
    O.equiv (Local.assemblyOrder P lay z) (Incidents.SiteOrder.eq_assembly («S»:=S) (w:=W) P (B).order lay z fit O)).symm

/-- The archive's old width span also bounds the positive key that labels every active motif.
This remains valid when the old width table starts at address zero. -/
theorem ShrinkOutput.rootKeys {W K : ℕ} {cur : Computability.VPVNP.BurstRAM.Word W}
    {m out : Computability.VPVNP.BurstRAM.Memory W} {c : NavigationDirectory.Cursor}
    {b : Fin (M).rules.count} (z : ShrinkOutput (K:=K) T s D rem hD small A cur m c b out) :
    ∀ a, Demand.key P (baseNat (B).order) a+1<2^W := by
  intro a
  let x:=Resident.dims S (Fintype.card (B).Base) t rem
  have bound:=SlotImage.edgeOrdinal_lt (B).order (Demand.laneOrdinal P) (packedAddress.symm a)
  rw [Demand.edge_address] at bound
  change Demand.key P (baseNat (B).order) a<x.oldEdges*x.originalLanes at bound
  have widths : c.width+x.oldEdges*x.originalLanes≤c.heap := z.cursor.widths
  have top := z.cursor.controls
  rw [NavigationDirectory.heap_step] at top
  have := cur.isLt
  omega


end ThreeFlat.Diagonal.PhysicalStage
end

end OAI
