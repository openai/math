import OAI.ThreeFlat.RAM.HistoryShrinkPlacement
import OAI.ThreeFlat.RAM.HistoryShrinkIncidentRecords

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open private large_stride from OAI.ThreeFlat.RAM.HistoryShrinkPlacement
open Computability.VPVNP.BurstRAM Diagonal.TickWorkspace HistoryStageBody.Physical HistoryScratch
open HistoryMotifJoin HistoryGatherBody HistoryPartyBatchExec
open scoped Fin.CommRing
noncomputable section
variable {u : ℕ} {A : Layout} {m : Memory (16*u^10)}
local notation "V" => volume u
local notation "W" => (16*u^10)

/-- Header and child directory loads come from the control word or retained
high RAM. Old child results occupy the bounded S13 array. -/
def publishedCell (u i : ℕ) : Prop := i=base u 18 ∨ base u 19≤ i

private theorem nodeReads_mono {lo hi : ℕ→Prop} (h : NodeReadCells A.nodePorts m lo)
    (f : ∀ i,lo i→hi i) : NodeReadCells A.nodePorts m hi :=
  ⟨f _ h.cursor,fun j=>f _ (h.node j),fun j=>f _ (h.header j),fun j=>f _ (h.tail j)⟩

private theorem motifReads_mono {lo hi : ℕ→Prop} (h : MotifReadCells A m lo)
    (f : ∀ i,lo i→hi i) : MotifReadCells A m hi :=
  ⟨fun j=>f _ (h.kernel j),fun j=>f _ (h.incident j)⟩

theorem privateHeader_physical (banks : PhysicalBanks u A) (vbig : 128≤V)
    (N : NodeReadCells A.nodePorts m (publishedCell u))
    (M : MotifReadCells A m (fun a=>base u 19≤a))
    (I : PrivateReadCells A m (fun a=>base u 19≤a)) :
    Protected (privateHeader A W) m A.privateStarts 9 := by
  let safe:=fun i=>i<A.privateStarts ∨ A.privateStarts+9≤ i
  have gap:=apart (u:=u) (by decide : 18<19)
  have size : 10*V≤ Diagonal.TickWorkspace.stride u:=large_stride (show 16≤V by omega)
  have high (i:ℕ) (h:base u 19≤ i) : safe i:=by dsimp [safe];rw [banks.privateStarts];omega
  have route (i:ℕ) (h:publishedCell u i) : safe i:=by
    rcases h with rfl|h
    · dsimp [safe];rw [banks.privateStarts];omega
    · exact high _ h
  exact privateHeader_protected A m (nodeReads_mono N route) (motifReads_mono M high)
    ⟨fun g h j=>high _ (I.stage g h j),fun g h j=>high _ (I.width g h j)⟩

/-- The assignment space covers all raw candidate Info[1] loads, including the
default address computed in an unused selector slot. -/
theorem joinHeader_physical (banks : PhysicalBanks u A) (age : 16≤u) (vbig : 128≤V)
    (g : Bool) (node : ℕ) (nodeBound : node<V^2)
    (volumeFit : (A.party.motifs+2)*(A.party.parties+2)*8*32≤V)
    (party : 0<A.party.parties) (motif : g=true→A.party.motif<A.party.motifs)
    (N : NodeReadCells A.nodePorts m (publishedCell u)) (M : MotifReadCells A m (fun a=>base u 19≤a))
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W))
    (children : (wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 4).val≤V) :
    Protected (joinHeader A W g) m (A.party.seed+64) (rows A W g).length := by
  let safe:=fun i=>i<A.party.seed+64 ∨ A.party.seed+64+(rows A W g).length≤ i
  have cap : (if g then A.party.parties else A.party.motifs)≤V := by
    have p : A.party.parties+2≤(A.party.motifs+2)*(A.party.parties+2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have q : A.party.motifs+2≤(A.party.motifs+2)*(A.party.parties+2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    cases g <;> simp <;>omega
  have len : (rows A W g).length=7+7*(if g then A.party.parties else A.party.motifs) :=
    HistoryMotifJoin.rows_len A g
  have width : 10*V≤Diagonal.TickWorkspace.stride u := large_stride (show 16≤V by omega)
  have low:=apart (u:=u) (by decide : 12<14)
  have far:=apart (u:=u) (by decide : 14<18)
  have top:=apart (u:=u) (by decide : 18<19)
  have fit:=word_space (u:=u) (i:=18) (by omega) (by omega)
  have high (i : ℕ) (h : base u 18≤ i) : safe i := by
    right
    rw [banks.seed,len]
    omega
  have known (i : ℕ) (h : publishedCell u i) : safe i := by rcases h with rfl|h <;>apply high <;>omega
  apply joinHeader_protected A m g node (nodeReads_mono (A:=A) N known)
    (motifReads_mono (A:=A) M (fun i h=>high i (by omega)))
  refine ⟨cursor,?_,?_,?_⟩
  · let n:=wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 4
    have nBound : n.val≤V := children
    have bound : A.nodePorts.starts+n.val<2^W:=by rw [banks.childStarts];omega
    change safe ((A.nodePorts.starts:Word W)+n).val
    have starts : (A.nodePorts.starts:Word W).val=A.nodePorts.starts := Fin.val_cast_of_lt (by omega)
    have sumFit : (A.nodePorts.starts:Word W).val+n.val<2^W := by rw [starts];exact bound
    rw [Fin.val_add_eq_of_add_lt sumFit,starts];apply high;rw [banks.childStarts];omega
  · intro _
    have room : A.privateStarts+8<2^W:=by rw [banks.privateStarts];omega
    rw [Fin.val_cast_of_lt room];apply high;rw [banks.privateStarts];omega
  · intro i hi j hj
    let loc : Local:=if g then ⟨A.party.motif+2,j+2,2,1⟩ else ⟨i+2,0,3,1⟩
    have ok : loc.Valid A.party.motifs A.party.parties:=by
      by_cases group : g=true
      · have roleBound : j<A.party.parties := by rcases hj with rfl|h <;> assumption
        simp only [loc,ite_eq_left group]
        change A.party.motif+2<A.party.motifs+2 ∧ j+2<A.party.parties+2 ∧ 2<8 ∧ 1<32
        exact ⟨Nat.add_lt_add_right (motif group) 2,Nat.add_lt_add_right roleBound 2,by decide,by decide⟩
      · have slotBound : i<A.party.motifs := by simpa only [ite_eq_right group] using hi
        simp only [loc,ite_eq_right group]
        change i+2<A.party.motifs+2 ∧ 0<A.party.parties+2 ∧ 3<8 ∧ 1<32
        exact ⟨Nat.add_lt_add_right slotBound 2,by omega,by decide,by decide⟩
    have cap := HistoryScratch.fits (base:=A.party.arena) nodeBound volumeFit ok (by omega : 1<V)
    have eq : sourceBank A node g i j 1+1=atWord A.party.arena V A.party.motifs A.party.parties node loc 1 := by
      cases g <;>simp [sourceBank,bankAddr,loc,atWord,banks.wordCount]
    rw [←eq,banks.arena] at cap
    change sourceBank A node g i j 1+1<base u 12+Diagonal.TickWorkspace.stride u at cap
    have small : sourceBank A node g i j 1+1<2^W:=by omega
    change safe (((sourceBank A node g i j 1:Word W)+1).val)
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt small]
    dsimp [safe];rw [banks.seed];omega

theorem childPrefix_physical (banks : PhysicalBanks u A) (vbig : 128≤V) (cap : ℕ) (small : cap≤V)
    (cells : ChildReadCells A.nodePorts m cap (fun i=>publishedCell u i ∨ i<base u 14)) :
    Protected (HeaderScan.closed (childPrefix A.nodePorts cap)) m A.nodePorts.starts (cap+1) := by
  let safe:=fun i=>i<A.nodePorts.starts ∨ A.nodePorts.starts+(cap+1)≤ i
  have high:=apart (u:=u) (by decide : 18<19)
  have low:=apart (u:=u) (by decide : 14<18)
  have width : 10*V≤ Diagonal.TickWorkspace.stride u:=large_stride (show 16≤V by omega)
  have t (i:ℕ) (h : publishedCell u i ∨ i<base u 14) : safe i:=by
    dsimp [safe];rw [banks.childStarts];rcases h with (rfl|h)|h <;>omega
  exact childPrefix_protected A.nodePorts cap m
    ⟨t _ cells.cursor,fun j=>t _ (cells.directory j),fun j=>t _ (cells.list j),fun j k=>t _ (cells.cache j k)⟩

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM HistoryGatherBody HistoryMotifJoin HistoryStageBody.Physical
open Diagonal.TickWorkspace Diagonal.PhysicalStage NavigationNodeRows HistoryPartyBatchExec
open scoped Fin.CommRing
noncomputable section
variable {u : ℕ} {A : HistoryGatherBody.Layout} {m : Memory (16*u^10)}
local notation "W" => (16*u^10)
local notation "V" => volume u

theorem directory_address_space (age : 16≤u) (vbig : 128≤V) {node : ℕ}
    (h : node<V^2) : base u 44+8*node+8<2^W := by
  have big : 16*V^2≤ Diagonal.TickWorkspace.stride u:=by
    change 16*V^2≤V^4
    have v2 : 16≤V^2:=by nlinarith
    calc _ ≤ V^2*V^2:=Nat.mul_le_mul_right _ v2
         _ = V^4:=by ring
  have volumeSq : V ≤ V^2 := Nat.le_self_pow (by decide : 2≠0) V
  have fit:=word_space (u:=u) (i:=44) (by omega) (by omega)
  omega

/-- Recover the header and the possibly indirect final-width addresses from the very
same archive row that the numbered S44 node selected. -/
theorem NodeReadCells.of_archive {d l : ℕ} {X : State d l} (O : X.ArchiveSites) (z : X.Site)
    (age : 16≤u) (vbig : 128≤V) (positive : 0<d) (node : ℕ) (nodeBound : node<V^2)
    (cursor : A.nodePorts.cursor=base u 18)
    (address : HistoryMotifJoin.nodeAddress A.nodePorts m=((base u 44+8*node:ℕ):Word W))
    (half : State.HalfRows O (fun i=>base u 19≤ i ∧ i<2^W) (numeric m))
    (point : wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 6=
      ((O.layer.incident+(O.ord z).val*2:ℕ):Word W)) :
    NodeReadCells A.nodePorts m (publishedCell u) := by
  let H:=O.layer.incident+(O.ord z).val*2
  let last:Fin (2*d):=⟨2*d-1,by omega⟩
  let ptr:=(m (H+1)).val
  have fit:=directory_address_space (u:=u) age vbig nodeBound
  have old:=apart (u:=u) (by decide : 18<44)
  have later:=apart (u:=u) (by decide : 19<44)
  have hfit : H<2^W:=(half.headerSafe z 0).2
  have val : (m H).val=2*d:=half.count z
  have one : (1:Word W).val=1:=Fin.val_cast_of_lt (by omega : 1<2^W)
  have ge : (1:Word W)≤ m H:=by change (1:Word W).val≤(m H).val;rw [one,val];omega
  have num : cutWord (m H) 1=(last.val:Word W):=by
    apply Fin.ext
    have lt : last.val<2^W:=last.isLt.trans_le (by rw [←val];exact (m H).isLt.le)
    change (if (m H)<(1:Word W) then 0 else m H-1).val=_
    rw [ite_eq_right (not_lt.mpr ge),Fin.sub_val_of_le ge,val,one,Fin.val_cast_of_lt lt]
  have hdr (k : Fin 2) :
      (wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 6+(k.val:Word W)).val=H+k.val := by
    rw [point,←Nat.cast_add,Fin.val_cast_of_lt (half.headerSafe z k).2]
  have pointerWord :
      wordAt m (wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 6) 1=m (H+1) := by
    exact congrArg m (hdr ⟨1,by decide⟩)
  have lastAddr : lastHalfAddress A.nodePorts m=((ptr+4*last.val:ℕ):Word W) := by
    change wordAt m (wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 6) 1+
      4*cutWord (m (wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 6).val) 1=_
    rw [pointerWord,point,Fin.val_cast_of_lt hfit,num]
    simp [ptr,Nat.cast_add,Nat.cast_mul]
  refine ⟨Or.inl (by rw [cursor,Fin.val_cast_of_lt (by omega)]),?_,?_,?_⟩
  · intro j
    rw [address,←Nat.cast_add,Fin.val_cast_of_lt (by have:=j.isLt;omega)]
    exact Or.inr (by omega)
  · intro j;rw [hdr];exact Or.inr (half.headerSafe z j).1
  · intro j
    let k:Fin 4:=⟨j.val+2,by have:=j.isLt;omega⟩
    have g:=half.entriesSafe z last k
    change base u 19≤ptr+4*last.val+(j.val+2) ∧ ptr+4*last.val+(j.val+2)<2^W at g
    rw [lastAddr,←Nat.cast_add,Fin.val_cast_of_lt g.2]
    exact .inr g.1

/-- The child-prefix scan probes one published ordered child vector. Each selected
child's S13 record has eight words and is below the S14 header arena. -/
theorem ChildReadCells.of_archive {s : Layer} (data : LayerData s) (j : Fin s.count)
    (age : 16≤u) (vbig : 128≤V) (node : ℕ) (nodeBound : node<V^2)
    (cursor : A.nodePorts.cursor=base u 18) (cache : A.nodePorts.cache=base u 13)
    (address : HistoryMotifJoin.nodeAddress A.nodePorts m=((base u 44+8*node:ℕ):Word W))
    (point : wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 3=((s.children+j.val*s.childCount:ℕ):Word W))
    (raw : data.Reads (numeric m)) (cells : data.Footprint (fun i=>base u 19≤ i ∧ i<2^W) (numeric m))
    (ids : ∀ k : Fin s.childCount,data.child j k<V^2) :
    ChildReadCells A.nodePorts m s.childCount (fun i=>publishedCell u i ∨ i<base u 14) := by
  have fit:=directory_address_space (u:=u) age vbig nodeBound
  have low:=apart (u:=u) (by decide : 13<14)
  have top:=apart (u:=u) (by decide : 19<44)
  have past:=apart (u:=u) (by decide : 18<44)
  have order:=apart (u:=u) (by decide : 14<44)
  have size : 16*V^2≤ Diagonal.TickWorkspace.stride u:=by
    change 16*V^2≤V^4
    calc _ ≤ V^2*V^2:=Nat.mul_le_mul_right _ (by nlinarith)
         _ = V^4:=by ring
  have ptr (k:Fin s.childCount) :
      (wordAt m (HistoryMotifJoin.nodeAddress A.nodePorts m) 3+(k.val:Word W)).val=s.children+j.val*s.childCount+k.val:=by
    rw [point,←Nat.cast_add,Fin.val_cast_of_lt (cells.child j k).2]
  refine ⟨Or.inl (Or.inl (by rw [cursor,Fin.val_cast_of_lt (by omega)])),?_,?_,?_⟩
  · intro k
    rw [address,←Nat.cast_add,Fin.val_cast_of_lt (by have:=k.isLt;omega)]
    exact Or.inl (Or.inr (by omega))
  · intro k;rw [ptr];exact Or.inl (Or.inr (cells.child j k).1)
  · intro k word q
    have id : word.val=data.child j k:=by change (m _).val=_;rw [ptr];exact raw.child j k
    have bound : A.nodePorts.cache+8*word.val+(1+4*q.val)<base u 14:=by
      rw [id,cache];have:=ids k;have:=q.isLt;omega
    change publishedCell u _ ∨ ((A.nodePorts.cache:Word W)+8*word+((1+4*q.val:ℕ):Word W)).val<_
    right
    have cast : (A.nodePorts.cache:Word W)+8*word+((1+4*q.val:ℕ):Word W)=
        ((A.nodePorts.cache+8*word.val+(1+4*q.val):ℕ):Word W) := by simp [Nat.cast_add,Nat.cast_mul]
    rw [cast,Fin.val_cast_of_lt (by omega)]
    exact bound

end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM Diagonal.TickWorkspace Diagonal.NavigationDirectory Diagonal.NavigationPass
open Diagonal.CompressorPacking Diagonal.CompressorPacking.Native HistoryMotifJoin HistoryGatherBody
open HistoryStageBody.Physical HistoryPartyBatchExec
open scoped Fin.CommRing
noncomputable section
variable {u : ℕ} {A : HistoryGatherBody.Layout} {m : Memory (16*u^10)}
local notation "W" => (16*u^10)

theorem nodeAddress_at (bank : A.nodePorts.nodes=base u 44) {node : ℕ}
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W)) :
    HistoryMotifJoin.nodeAddress A.nodePorts m=((base u 44+8*node:ℕ):Word W) := by
  change (A.nodePorts.nodes:Word W)+8*(HistoryNodePorts.id A.nodePorts).value _ m (fun _=>0)=_
  rw [cursor,bank];simp [Nat.cast_add,Nat.cast_mul]

private theorem descriptorAllocation (K : ℕ) (c : Cursor) (op : Stage) :
    let e:=allocate K c op
    c.heap≤e.words 34 ∧ e.words 34+5*(successors op)≤e.next.heap ∧
      c.heap≤e.words 36 ∧ e.words 36+6*(stageMotifs op)*(successors op)≤e.next.heap := by
  cases op <;>simp [allocate,successors,stageMotifs,ShrinkStage.headerExtra,ShrinkStage.extraEnd,
    Diagonal.RefreshStageLayout.headerExtra,Diagonal.RefreshStageLayout.extraEnd,Nat.add_mul,Nat.mul_add] <;> omega

/-- Both families reserve a full dense block of local candidate records. This
covers every six-word descriptor touched when enumerating the cap, even after
the last live motif of the current successor. -/
theorem motifCells_at_stage (K : ℕ) (c : Cursor) (op : Stage)
    (n : Fin (successors op)) (j : Fin (stageMotifs op))
    (before : base u 19≤c.heap) (fit : (allocate K c op).next.heap≤2^W)
    (kernel : (selected A m).kernel=(((allocate K c op).words 34+n.val*5:ℕ):Word W))
    (incident : (selected A m).incident=
      (((allocate K c op).words 36+6*(stageMotifs op*n.val+j.val):ℕ):Word W)) :
    MotifReadCells A m (fun i=>base u 19≤ i) := by
  let e:=allocate K c op
  obtain ⟨loK,hiK,loI,hiI⟩:=descriptorAllocation K c op
  apply MotifReadCells.of_addresses A _ _ kernel incident
  · intro a
    have h:=ShrinkStage.DescriptorSpan.half_index_lt n.isLt a.isLt
    rw [Nat.mul_comm 5 (successors op)] at hiK
    omega
  · intro a
    have h:=ShrinkStage.DescriptorSpan.half_index_lt (ShrinkStage.DescriptorSpan.half_index_lt n.isLt j.isLt) a.isLt
    have eq : 6*(stageMotifs op*n.val+j.val)+a.val<(6*stageMotifs op)*(successors op) := by
      convert h using 1 <;> ring
    omega

/-- In a selected shrink the issued widths start at the third common stage
array. The histogram row ID selects exactly its own eight-word block. -/
theorem shrinkPrivateCells_at_stage {owns : Fin 8→Prop} {issued : Fin 8→ℕ}
    {geo : Diagonal.CompressorPacking.Native.Graph.Stage} (r : PrivateSite A (geo:=geo) m owns issued)
    (K : ℕ) (c : Cursor) (x : ShrinkStage.Dimensions)
    (high : base u 19≤c.header) (earlier : c.header+64≤c.heap)
    (fit : (allocate K c (.shrink x)).next.heap≤2^W)
    (stage : m (selected A m).kernel.val=(c.header:Word W))
    (ptr : r.supply=(allocate K c (.shrink x)).words 3) :
    PrivateReadCells A m (fun i=>base u 19≤ i) := by
  have done:=heap_step K c (.shrink x)
  apply PrivateReadCells.of_shrink A r c.header stage
  · intro i;have:=i.isLt;omega
  · intro i
    have low : c.heap≤(allocate K c (.shrink x)).words 3 := by
      simp [allocate,ShrinkStage.headerWord]
    rw [ptr]
    omega


end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr Computability.VPVNP.Compression
open Diagonal Diagonal.PhysicalStage Diagonal.CompressorPacking Diagonal.CompressorPacking.PhysicalShrink
open Diagonal.CompressorPacking.Native Diagonal.CompressorPacking.Native.ShrinkStage
open Diagonal.NavigationDirectory Diagonal.NavigationPass Diagonal.ShrinkStageNav Diagonal.TickWorkspace
open HistoryStageBody.Physical HistoryGatherBody HistoryRefreshEmitter HistoryPartyBatchExec
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) (u : ℕ) (arch : HistoryStageBody.Physical.Archive) (family : Family) (node : ℕ)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "T" => B.shrink
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B₀" => shrinkRecordState s rem A
local notation "N" => Fintype.card (B₀).Base
local notation "P" => shrinkRecordPacking s rem A
local notation "t₀" => Diagonal.CompressorPacking.tagBits (2^s)
local notation "S" => shrinkStage s D
local notation "x₀" => Resident.dims S N t₀ rem
variable {K : ℕ} (cur ctr : Word (16*u^10)) (before issued final input : Memory (16*u^10)) (c : Cursor)
    (branch : Fin (shrinkBinary B.shrink s D rem hD small A).rules.count)
local notation "lay" => ShrinkMotif.chooseWidths (shrinkIssuedWords T s D rem hD small A branch)
local notation "en" => allocate K c (.shrink x₀)
local notation "fields_" => DescriptorSpan.fields K c x₀ lay
variable (hdr : ℕ) (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved : let x := Resident.dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base)
                       (Diagonal.CompressorPacking.tagBits (2^s)) rem
             let next := (allocate K c (.shrink x)).next
             SavedFrame cur ctr hdr next.header next.heap issued final)
    (site : Computability.VPVNP.Compression.Site (shrinkRecordState s rem A).Base
      (BitWord (Diagonal.CompressorPacking.tagBits (2^s))) (BitWord rem))
    (O : Incidents.SiteOrder («S»:=shrinkStage s D) (shrinkRecordPacking s rem A)
      (shrinkRecordState s rem A).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) site (16*u^10))
local notation "sn" => Incidents.siteNumber (B₀).order site
local notation "cap" => Incidents.capacity S
local notation "kernelBase" => (fields_ 34+5*sn : ℕ)
local notation "incidentBase" => (fields_ 36+sn*(6*cap) : ℕ)
local notation "actual" => (Incidents.siteKeys («S»:=S) (w:=W) P (B₀).order lay site).length
local notation "baseNode" => (base u 44+8*node : ℕ)
variable (g : ℕ) (j : Fin family.parties)
local notation "arm" => rawParty (layout u arch family) g j.val

private theorem shrink_volume_large {u : ℕ} (age : 16 ≤ u) : 128 ≤ volume u := by
  have linear : u ≤ u ^ 10 := Nat.le_self_pow (by decide : 10 ≠ 0) u
  have exponent : 7 ≤ u ^ 10 := (by omega : 7 ≤ u).trans linear
  change (2 : ℕ)^7 ≤ 2^(u^10)
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) exponent

include H saved O in
set_option maxRecDepth 19000 in
omit [Fintype F] in
/-- Both numerical address interpreters read the same active incidence record from
the issued shrink layer, through the retained physical S44 node header. -/
theorem recorded_occupied_header (oldCaps : ShrinkOldCaps s rem W) (baseFit : N≤2^W)
    (wide : 8≤W) (capFits : cap<2^W) (offset : 0<c.width)
    (guard : ∀ a,hdr≤a→a<(en).next.heap→a≠cur.val ∧ a≠ctr.val)
    (savedWords : ∀ a,hdr≤a→a<(en).next.heap→input a=final a)
    (lowKernel : hdr≤fields_ 34) (lowRows : hdr≤fields_ 36) (above : base u 19≤hdr)
    (cursor : numeric input (base u 18)-1=node)
    (nodeHead : input (baseNode+5)=(kernelBase:Word W))
    (age : 16≤u) (count : node<V^2) (live : g<actual) :
    let row:=fields_ 36+6*(cap*sn+g)
    HistoryPartyBatch.kernel (arm).party (numeric input)=kernelBase ∧
      HistoryPartyBatch.incident (arm).party (numeric input)=row ∧
      g<numeric input (HistoryPartyBatch.kernel (arm).party (numeric input)+3) ∧
      (selected arm input).incident=(row:Word W) ∧ (selected arm input).kernel=(kernelBase:Word W) ∧
      archiveWindow u kernelBase 5 ∧ archiveWindow u row 6 ∧ archiveWindow u baseNode 8 ∧
      (∀i:Fin 5,hdr≤kernelBase+i.val ∧ kernelBase+i.val<(en).next.heap) ∧
      (∀i:Fin 6,hdr≤ row+i.val ∧ row+i.val<(en).next.heap) := by
  have upper : (en).next.heap<2^W:=H.cursor.controls.trans_lt cur.isLt
  have kernel (i : Fin 5) :
      kernelBase+i.val<(en).next.heap ∧ input (kernelBase+i.val)=
        ((![c.header,sn,1,actual,incidentBase] : Fin 5→ℕ) i:Word W) ∧ actual≤cap := by
    have written:=ShrinkOutput.selected_kernel T s D rem hD small A cur before c branch H oldCaps baseFit wide
      capFits offset site i
    have address : kernelBase + i.val = fields_ 34 + (5 * sn + i.val) := Nat.add_assoc _ _ _
    have below : kernelBase + i.val < (en).next.heap := address.trans_lt written.1
    have lower : hdr ≤ kernelBase + i.val :=
      (lowKernel.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
    obtain ⟨a,b⟩ := guard _ lower below
    exact ⟨below, (savedWords _ lower below).trans
      ((saved _ a b (.inr lower) below).trans ((congrArg issued address).trans written.2.1)), written.2.2⟩
  have actualFit : actual<2^W:=(kernel 3).2.2.trans_lt capFits
  have kernelCount : input (kernelBase+3)=(actual : Word W):=(kernel 3).2.1
  have kernelIncident : input (kernelBase+4)=(incidentBase : Word W):=(kernel 4).2.1
  have kfit : kernelBase+4<2^W:=(kernel 4).1.trans upper
  have vbig : 128 ≤ V := shrink_volume_large age
  have nf:=directory_address_space (u:=u) age vbig count
  have gap:=apart (u:=u) (by decide : 18<44)
  have cfit : base u 18<2^W:=by omega
  have raw (k : Fin 6) (live : g<actual) :
      fields_ 36+6*(cap*sn+g)+k.val<(en).next.heap := by
    have selectedDescriptor:=ShrinkOutput.selected_descriptor T s D rem hD small A cur before c branch H
      oldCaps baseFit wide capFits offset site O ⟨g,live⟩ k
    simpa only [Nat.add_assoc] using selectedDescriptor.1
  have equality : incidentBase+6*g=fields_ 36+6*(cap*sn+g) := by ring
  have activeEnd (live : g<actual) : incidentBase+6*g+5<(en).next.heap:=by rw [equality];exact raw 5 live
  have selectedKernel : (selected arm input).kernel=(kernelBase:Word W) := by
    have fit : (HistoryNodePorts.id (arm).nodePorts).Fits W (fun _=>0) (numeric input) (fun _=>0):=
      ⟨⟨trivial,cfit⟩,trivial,(input (base u 18)).isLt,by change 1<2^W;omega⟩
    have eval:=Formula.value_eq_natural (HistoryNodePorts.id (arm).nodePorts) (fun _=>0) (numeric input) (fun _=>0) fit
    rw [word_numeric] at eval
    have val : (HistoryNodePorts.id (arm).nodePorts).value (fun _=>0) input (fun _=>0)=(node:Word W):=by
      exact eval.trans (congrArg (fun k : ℕ => (k : Word W)) cursor)
    have nd : nodeWord arm input=((base u 44+8*node : ℕ):Word W):=by
      change (base u 44:Word W)+8*((HistoryNodePorts.id (arm).nodePorts).value (fun _=>0) input (fun _=>0))=_
      simp only [val,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    change input (nodeWord arm input+5).val=_
    rw [nd,show (5:Word W)=((5:ℕ):Word W) from rfl,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    exact nodeHead
  have rk : HistoryPartyBatch.kernel (arm).party (numeric input)=kernelBase := by
    change numeric input (base u 44+8*(numeric input (base u 18)-1)+5)=_
    rw [cursor]
    exact (congrArg Fin.val nodeHead).trans (Fin.val_cast_of_lt (by omega))
  have ptrFit : incidentBase<2^W := by have h:=activeEnd live; omega
  have nr : HistoryPartyBatch.incident (arm).party (numeric input)=fields_ 36+6*(cap*sn+g) := by
    unfold HistoryPartyBatch.incident
    rw [rk]
    change (input (kernelBase+4)).val+6*g=_
    rw [kernelIncident,Fin.val_cast_of_lt ptrFit,equality]
  have row : (selected arm input).incident=((fields_ 36+6*(cap*sn+g):ℕ):Word W) := by
    change input ((selected arm input).kernel+4).val+(6*g:ℕ)=_
    rw [selectedKernel,show (4:Word W)=((4:ℕ):Word W) from rfl,←Nat.cast_add,Fin.val_cast_of_lt kfit]
    rw [kernelIncident]
    rw [←Nat.cast_add,equality]
  have oldRegion := TickWorkspace.apart (u:=u) (by decide:18<19)
  have nodeRegion := TickWorkspace.apart (u:=u) (by decide:18<44)
  refine ⟨rk,nr,?_,row,selectedKernel,⟨?_,.inr (by omega)⟩,⟨?_,.inr (by omega)⟩,
    ⟨nf,.inr (by omega)⟩,fun i=>⟨by omega,(kernel i).1⟩,fun i=>⟨by omega,raw i live⟩⟩
  · rw [rk]
    change g<(input (kernelBase+3)).val
    rw [kernelCount,Fin.val_cast_of_lt actualFit];exact live
  · have h:=(kernel 4).1;omega
  · have h:=raw 5 live;omega

private theorem absentAtWord {width : ℕ} (mem : Memory width) (pointer : Word width)
    (addr column : ℕ) (atWord : pointer=(addr:Word width)) (fits : addr+5<2^width)
    {p : Prop} {decision : Decidable p}
    (read : (wordAt mem pointer 5).val.testBit column = @decide p decision)
    (absent : ¬ p) : (mem (addr+5)).val.testBit column=false := by
  have address : (pointer+((5:ℕ):Word width)).val=addr+5 := by
    rw [atWord,←Nat.cast_add,Fin.val_cast_of_lt fits]
  change (mem (pointer+((5:ℕ):Word width)).val).val.testBit column=_ at read
  rw [address] at read
  exact read.trans (@decide_eq_false p decision absent)

include H saved in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 19000 in
omit [Fintype F] in
/-- The vacant arm of the actual selected shrink. Only a motif below the stored
incident count opens a descriptor row. The same archived fields survive every
preceding party update via the immutable low/high address frame. -/
theorem recorded_vacant_room (oldCaps : ShrinkOldCaps s rem W) (baseFit : N≤2^W)
    (wide : 8≤W) (capFits : cap<2^W) (offset : 0<c.width)
    (guard : ∀ a,hdr≤a→a<(en).next.heap→a≠cur.val ∧ a≠ctr.val)
    (savedWords : ∀ a,hdr≤a→a<(en).next.heap→input a=final a)
    (lowKernel : hdr≤fields_ 34) (lowRows : hdr≤fields_ 36) (above : base u 18≤hdr)
    (cursor : numeric input (base u 18)-1=node)
    (nodeHead : input (baseNode+5)=(kernelBase:Word W))
    (parties : family.parties=6)
    (unused : ∀ h : g<actual,partySite P lay (O.equiv ⟨g,h⟩).val (j.cast parties)≠site)
    (encode : ((Fin 3→Bool)→F)→ℕ)
    (age : 16≤u) (count : node<V^2) (motifs : g<family.motifs)
    (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V) (mask : 2^family.parties<2^W)
    (lookup : arch.lut+1<2^W) (lutStride : arch.lutStride<2^W) (pages : arch.pages<2^W)
    (pageStride : arch.pageStride<2^W) (counts : arch.counts+1<2^W)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (headerCap : 3+5*family.demands+4*family.supplies≤V)
    (ports : HistoryGatherExecution.portsEnd arm<2^W) :
    VacantRoom arm node encode input ∧
    ∀ a,(readZone u a ∨ OutsideNode u node a)→vacantPass arm node encode input a=input a := by
  let maskVal:=numeric input (incidentBase+6*g+5)
  have upper : (en).next.heap<2^W:=H.cursor.controls.trans_lt cur.isLt
  have kernel (i : Fin 5) :
      kernelBase+i.val<(en).next.heap ∧ input (kernelBase+i.val)=
        ((![c.header,sn,1,actual,incidentBase] : Fin 5→ℕ) i:Word W) ∧ actual≤cap := by
    have written:=ShrinkOutput.selected_kernel T s D rem hD small A cur before c branch H oldCaps baseFit wide
      capFits offset site i
    have address : kernelBase + i.val = fields_ 34 + (5 * sn + i.val) := Nat.add_assoc _ _ _
    have below : kernelBase + i.val < (en).next.heap := address.trans_lt written.1
    have lower : hdr ≤ kernelBase + i.val :=
      (lowKernel.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
    obtain ⟨a,b⟩ := guard _ lower below
    exact ⟨below, (savedWords _ lower below).trans
      ((saved _ a b (.inr lower) below).trans ((congrArg issued address).trans written.2.1)), written.2.2⟩
  have actualFit : actual<2^W:=(kernel 3).2.2.trans_lt capFits
  have kernelCount : input (kernelBase+3)=(actual : Word W):=(kernel 3).2.1
  have kernelIncident : input (kernelBase+4)=(incidentBase : Word W):=(kernel 4).2.1
  have kfit : kernelBase+4<2^W:=(kernel 4).1.trans upper
  have vbig : 128 ≤ V := shrink_volume_large age
  have nf:=directory_address_space (u:=u) age vbig count
  have gap:=apart (u:=u) (by decide : 18<44)
  have cfit : base u 18<2^W:=by omega
  have raw (k : Fin 6) (live : g<actual) :
      fields_ 36+6*(cap*sn+g)+k.val<(en).next.heap := by
    have selectedDescriptor:=ShrinkOutput.selected_descriptor T s D rem hD small A cur before c branch H
      oldCaps baseFit wide capFits offset site O ⟨g,live⟩ k
    simpa only [Nat.add_assoc] using selectedDescriptor.1
  have equality : incidentBase+6*g=fields_ 36+6*(cap*sn+g) := by ring
  have activeEnd (live : g<actual) : incidentBase+6*g+5<(en).next.heap:=by rw [equality];exact raw 5 live
  have room : DormantRoom u node kernelBase incidentBase g actual := by
    refine ⟨cfit,by omega,(kernel 3).1.trans upper,.inr (by omega),.inr (by omega),
      fun _=>⟨kfit,.inr (by omega)⟩,fun h=>⟨(activeEnd h).trans upper,.inr (by omega)⟩⟩
  have selectedKernel : (selected arm input).kernel=(kernelBase:Word W) := by
    have fit : (HistoryNodePorts.id (arm).nodePorts).Fits W (fun _=>0) (numeric input) (fun _=>0):=
      ⟨⟨trivial,cfit⟩,trivial,(input (base u 18)).isLt,by change 1<2^W;omega⟩
    have eval:=Formula.value_eq_natural (HistoryNodePorts.id (arm).nodePorts) (fun _=>0) (numeric input) (fun _=>0) fit
    rw [word_numeric] at eval
    have val : (HistoryNodePorts.id (arm).nodePorts).value (fun _=>0) input (fun _=>0)=(node:Word W):=by
      exact eval.trans (congrArg (fun k : ℕ => (k : Word W)) cursor)
    have nd : nodeWord arm input=((base u 44+8*node : ℕ):Word W):=by
      change (base u 44:Word W)+8*((HistoryNodePorts.id (arm).nodePorts).value (fun _=>0) input (fun _=>0))=_
      simp only [val,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    change input (nodeWord arm input+5).val=_
    rw [nd,show (5:Word W)=((5:ℕ):Word W) from rfl,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    exact nodeHead
  have origin : DormantRead u node input kernelBase incidentBase g actual maskVal j.val := by
    refine ⟨cursor,(congrArg Fin.val nodeHead).trans (Fin.val_cast_of_lt (by omega)),?_,?_,fun _=>rfl,?_⟩
    · exact (congrArg Fin.val kernelCount).trans (Fin.val_cast_of_lt actualFit)
    · intro h
      have ptrFit : incidentBase<2^W := by have:=activeEnd h;omega
      exact (congrArg Fin.val kernelIncident).trans (Fin.val_cast_of_lt ptrFit)
    · intro h
      have guards (k : Fin 6) :
          fields_ 36+6*(cap*sn+g)+k.val≠cur.val ∧ fields_ 36+6*(cap*sn+g)+k.val≠ctr.val ∧
          hdr≤fields_ 36+6*(cap*sn+g)+k.val := by
        have lo : hdr≤fields_ 36+6*(cap*sn+g)+k.val:=by omega
        obtain ⟨a,b⟩:=guard _ lo (raw k h)
        exact ⟨a,b,lo⟩
      have keep (k : Fin 6) : input (fields_ 36+6*(cap*sn+g)+k.val)=final (fields_ 36+6*(cap*sn+g)+k.val):=
        savedWords _ (guards k).2.2 (raw k h)
      have row : (selected arm input).incident=((fields_ 36+6*(cap*sn+g):ℕ):Word W) := by
        change input ((selected arm input).kernel+4).val+(6*g:ℕ)=_
        rw [selectedKernel,show (4:Word W)=((4:ℕ):Word W) from rfl,←Nat.cast_add,Fin.val_cast_of_lt kfit]
        rw [kernelIncident]
        rw [←Nat.cast_add,equality]
      have fields:=recorded_fields B s D rem hD small A cur ctr before issued final input c branch hdr H saved
        site O ⟨g,h⟩ arm oldCaps baseFit wide capFits offset row guards keep (j.cast parties)
      change (input (incidentBase+6*g+5)).val.testBit j.val=false
      rw [equality]
      exact absentAtWord input (selected arm input).incident _ j.val row
        ((raw 5 h).trans upper) fields.2.2.2 (unused h)
  exact physical_dormant_room u arch family node j input kernelBase incidentBase g actual maskVal
    encode origin room age count motifs capacity mask lookup lutStride pages pageStride counts lutAway countsAway headerCap ports

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
