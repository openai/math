import OAI.ThreeFlat.RAM.HistoryRefreshPlacement

namespace OAI
/-! # Refresh incidence reads and vacant party memory -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

section PhysicalOrder
open HistoryStageBody.Physical Diagonal.TickWorkspace HistoryScratch
variable (u : ℕ) (arch : HistoryStageBody.Physical.Archive) (f : Family) (node : ℕ) (winner : Fin f.parties)
local notation "A" => layout u arch f
local notation "V" => volume u
local notation "W₀" => 16*u^10

section Incidence
open HistoryGatherBody
variable (j : Fin f.parties) (mem : Memory (16*u^10)) (kernelPtr incidentPtr : ℕ)
local notation "Aⱼ" => rawArm A j.val
local notation "J" => (Aⱼ).party
local notation "nodePtr" => base u 44+8*node

/-- The immutable five physical cells used by an unoccupied refresh arm. The topology
can be either in the low descriptor area or in the upper geometric archive. -/
def readZone (u addr:ℕ) := addr<base u 12 ∨ base u 18≤addr

structure IncidenceRead : Prop where
  cursor : numeric mem (base u 18)-1=node
  kernel : numeric mem (base u 44+8*node+5)=kernelPtr
  count : 0<numeric mem (kernelPtr+3)
  incident : numeric mem (kernelPtr+4)=incidentPtr
  mask : numeric mem (incidentPtr+5)=2^winner.val

section NativeRecords
open Diagonal Diagonal.CompressorPacking.Native Diagonal.RefreshDemandRows Diagonal.RefreshStageNav
open Computability.VPVNP.Compression
variable {nv nc power degree : ℕ} (P : Records.Pointers) (head width : ℕ)
  (G : LiftedSlots (Fin nv × Fin nc) degree (BitWord power))
  (edge : SlotImage.Edge (Fin nv × Fin nc) (BitWord power) degree→ℕ)
  (prior : ℕ→ℕ) (site : Records.Site nv nc power)
local notation "n₀" => Records.siteId (site.1.1,site.2) site.1.2
local notation "b₀" => blockId (site.1.1,site.2)

/-- Re-read both actual archived rows at the mixed-radix site index published by navigation. -/
theorem refresh_record_words (kernelRows : Records.Reads mem P head width G edge prior .kernel)
    (motifRows : Records.Reads mem P head width G edge prior .motif) :
    (∀ c:Fin 5,mem (P.kernel+n₀*5+c.val)=
      ((![head,n₀,2,1,P.motif+n₀*6]:Fin 5→ℕ) c:Word W₀)) ∧
    (∀ c:Fin 6,mem (P.motif+n₀*6+c.val)=
      ((![b₀,P.counts+b₀*width,prior (P.choices+b₀*3+1),prior (P.choices+b₀*3),0,2^site.1.2.val]:Fin 6→ℕ) c:Word W₀)) := by
  constructor
  · intro c
    have hx:=kernelRows (site,c)
    have v : (Records.rowOrder degree .kernel (site,c)).val=n₀*5+c.val:=by
      rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val];rfl
    simpa [Records.Pointers.dst,Records.Table.value,v,Nat.add_assoc] using hx
  · intro c
    have hx:=motifRows (site,c)
    have v : (Records.rowOrder degree .motif (site,c)).val=n₀*6+c.val:=by
      rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val];rfl
    simpa [Records.Pointers.dst,Records.Table.value,v,Nat.add_assoc] using hx

/-- Navigation's native kernel and motif tables give both the selected mask and the
geometry pointer, using just the current S44 node and its chronological owner. -/
theorem incidence_from_records (kernelRows : Records.Reads mem P head width G edge prior .kernel)
    (motifRows : Records.Reads mem P head width G edge prior .motif)
    (cursor : numeric mem (base u 18)-1=node)
    (reported : numeric mem (nodePtr+5)=P.kernel+n₀*5) (owner : winner.val=site.1.2.val)
    (motifFit : P.motif+n₀*6<2^W₀) (maskRoom : 2^f.parties<2^W₀) :
    IncidenceRead u f node winner mem (P.kernel+n₀*5) (P.motif+n₀*6) := by
  obtain ⟨k,m⟩:=refresh_record_words u mem P head width G edge prior site kernelRows motifRows
  have bit : 2^winner.val<2^W₀:=(Nat.pow_le_pow_right (by decide : 0<2) winner.isLt.le).trans_lt maskRoom
  have one : 1<2^W₀:=lt_of_le_of_lt (Nat.one_le_pow _ _ (by decide : 0<2)) maskRoom
  refine ⟨cursor,reported,?_,?_,?_⟩
  · change 0<(mem (P.kernel+n₀*5+3)).val
    have e : mem (P.kernel+n₀*5+3)=((1:ℕ):Word W₀):=k 3
    rw [e,Fin.val_cast_of_lt one];decide
  · change (mem (P.kernel+n₀*5+4)).val=_
    have e : mem (P.kernel+n₀*5+4)=((P.motif+n₀*6:ℕ):Word W₀):=k 4
    rw [e,Fin.val_cast_of_lt motifFit]
  · change (mem (P.motif+n₀*6+5)).val=_
    have e : mem (P.motif+n₀*6+5)=((2^site.1.2.val:ℕ):Word W₀):=m 5
    rw [e,←owner,Fin.val_cast_of_lt bit]

/-- The other four incident reads in the elected branch are the actual histogram,
tile code, multiplicity and row ID from the native refresh motif. -/
theorem elected_record_fields (motifRows : Records.Reads mem P head width G edge prior .motif)
    (fit : ∀ c:Fin 4,(![b₀,P.counts+b₀*width,prior (P.choices+b₀*3+1),prior (P.choices+b₀*3)]:Fin 4→ℕ) c<2^W₀)
    (c:Fin 4) : numeric mem (P.motif+n₀*6+c.val)=
      (![b₀,P.counts+b₀*width,prior (P.choices+b₀*3+1),prior (P.choices+b₀*3)]:Fin 4→ℕ) c := by
  let k:Fin 6:=⟨c.val,c.isLt.trans (by decide)⟩
  have row:=motifRows (site,k)
  have off : (Records.rowOrder degree .motif (site,k)).val=n₀*6+c.val:=by
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val];rfl
  change (mem (P.motif+n₀*6+c.val)).val=_
  have disk : mem (P.motif+n₀*6+c.val)=
      (((![b₀,P.counts+b₀*width,prior (P.choices+b₀*3+1),prior (P.choices+b₀*3)]:Fin 4→ℕ) c:ℕ):Word W₀):=by
    rw [off] at row
    simpa only [Records.Pointers.dst,Records.Table.value,Nat.add_assoc] using
      (show mem (P.motif+(n₀*6+c.val))=_ from row).trans (by fin_cases c <;> rfl)
  rw [disk,Fin.val_cast_of_lt (fit c)]

end NativeRecords

structure IncidenceRoom : Prop where
  cursor : base u 18<2^W₀
  node : nodePtr+5<2^W₀
  kernel : kernelPtr+4<2^W₀
  incident : incidentPtr+5<2^W₀
  nodeArea : readZone u (nodePtr+5)
  kernelCount : readZone u (kernelPtr+3)
  kernelPtr : readZone u (kernelPtr+4)
  incidentMask : readZone u (incidentPtr+5)

/-- Frames of the five real cells suffice for all subsequent raw party instructions. -/
theorem IncidenceRead.keep {m q:Memory W₀}
    (read : IncidenceRead u f node winner m kernelPtr incidentPtr)
    (room : IncidenceRoom u node kernelPtr incidentPtr)
    (keep : ∀ a,readZone u a→q a=m a) :
    IncidenceRead u f node winner q kernelPtr incidentPtr := by
  have stays (a:ℕ) (h:readZone u a) : numeric q a=numeric m a:=congrArg Fin.val (keep a h)
  exact ⟨by rw [stays (base u 18) (.inr le_rfl)];exact read.cursor,
    (stays _ room.nodeArea).trans read.kernel,by rw [stays _ room.kernelCount];exact read.count,
    (stays _ room.kernelPtr).trans read.incident,(stays _ room.incidentMask).trans read.mask⟩

theorem IncidenceRead.batch (read : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (absent : j≠winner) (room : IncidenceRoom u node kernelPtr incidentPtr) (ck:Bool) :
    ¬occupied J (numeric mem) ∧
      ∀ x,HistoryPartyBootExec.SeedRead J ck (numeric mem) x→ readZone u x ∧ x<2^W₀ := by
  have ker : HistoryPartyBatch.kernel J (numeric mem)=kernelPtr:=by
    change numeric mem (base u 44+8*(numeric mem (base u 18)-1)+5)=_
    rw [read.cursor,read.kernel]
  have inc : HistoryPartyBatch.incident J (numeric mem)=incidentPtr:=by
    change numeric mem (HistoryPartyBatch.kernel J (numeric mem)+4)+6*0=_
    simpa only [ker,Nat.mul_zero,Nat.add_zero] using read.incident
  have one : 0<numeric mem (HistoryPartyBatch.kernel J (numeric mem)+3):=by rw [ker];exact read.count
  have mask : numeric mem (HistoryPartyBatch.incident J (numeric mem)+5)=2^winner.val:=by
    rw [inc];exact read.mask
  have off : ¬occupied J (numeric mem):=fun h=>absent (Fin.ext ((batch_occupied A mem winner j.val one mask).mp h))
  refine ⟨off,?_⟩
  intro x h
  cases h with
  | cursor => exact ⟨.inr le_rfl,room.cursor⟩
  | node =>
    change readZone u (base u 44+8*(numeric mem (base u 18)-1)+5) ∧
      base u 44+8*(numeric mem (base u 18)-1)+5<2^W₀
    rw [read.cursor]
    exact ⟨room.nodeArea,room.node⟩
  | motifCount => rw [ker];exact ⟨room.kernelCount,by have:=room.kernel;omega⟩
  | incidentPtr _ => rw [ker];exact ⟨room.kernelPtr,room.kernel⟩
  | partyMask _ => rw [inc];exact ⟨room.incidentMask,room.incident⟩
  | kindIndex h => exact (off h).elim
  | copyCount h => exact (off h).elim
  | digitWidth h => exact (off h).elim
  | kindCount h => exact (off h).elim

/-- Execute every actual elected seed probe. In addition to the five occupancy
words only two incident values and the selected resident kind row are read. -/
theorem IncidenceRead.elected (read : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (room : IncidenceRoom u node kernelPtr incidentPtr) (ck : Bool) (kindId : ℕ)
    (row : numeric mem (incidentPtr+2)=kindId) (incidentArea:archiveWindow u incidentPtr 6)
    (gridArea:archiveWindow u (f.kinds+7*(kindId*f.parties+winner.val)) 7) :
    let arm:=(rawArm A winner.val).party
    occupied arm (numeric mem) ∧ HistoryPartyBatch.incident arm (numeric mem)=incidentPtr ∧
      HistoryPartyBatch.shape arm (numeric mem)=f.kinds+7*(kindId*f.parties+winner.val) ∧
      ∀ x,HistoryPartyBootExec.SeedRead arm ck (numeric mem) x→ readZone u x ∧ x<2^W₀ := by
  intro arm
  have ker : HistoryPartyBatch.kernel arm (numeric mem)=kernelPtr:=by
    change numeric mem (base u 44+8*(numeric mem (base u 18)-1)+5)=_
    rw [read.cursor,read.kernel]
  have inc : HistoryPartyBatch.incident arm (numeric mem)=incidentPtr:=by
    change numeric mem (HistoryPartyBatch.kernel arm (numeric mem)+4)+6*0=_
    simpa only [ker,Nat.mul_zero,Nat.add_zero] using read.incident
  have sh : HistoryPartyBatch.shape arm (numeric mem)=f.kinds+7*(kindId*f.parties+winner.val):=by
    change f.kinds+7*(numeric mem (HistoryPartyBatch.incident arm (numeric mem)+2)*f.parties+winner.val)=_
    rw [inc,row]
  have one : 0<numeric mem (HistoryPartyBatch.kernel arm (numeric mem)+3):=by rw [ker];exact read.count
  have mask : numeric mem (HistoryPartyBatch.incident arm (numeric mem)+5)=2^winner.val:=by rw [inc];exact read.mask
  have yes : occupied arm (numeric mem):=(batch_occupied A mem winner winner.val one mask).mpr rfl
  have inside (b l t:ℕ) (span:archiveWindow u b l) (lt:t<l) : readZone u (b+t) ∧ b+t<2^W₀:=by
    rcases span with ⟨bound,lo|hi⟩
    · exact ⟨.inl (by omega),by omega⟩
    · exact ⟨.inr (by omega),by omega⟩
  refine ⟨yes,inc,sh,?_⟩
  intro x hx
  cases hx with
  | cursor => exact ⟨.inr le_rfl,room.cursor⟩
  | node =>
    change readZone u (base u 44+8*(numeric mem (base u 18)-1)+5) ∧
      base u 44+8*(numeric mem (base u 18)-1)+5<2^W₀
    rw [read.cursor]
    exact ⟨room.nodeArea,room.node⟩
  | motifCount => rw [ker];exact ⟨room.kernelCount,by have:=room.kernel;omega⟩
  | incidentPtr _ => rw [ker];exact ⟨room.kernelPtr,room.kernel⟩
  | partyMask _ => rw [inc];exact ⟨room.incidentMask,room.incident⟩
  | kindIndex _ => rw [inc];exact inside _ _ 2 incidentArea (by decide)
  | copyCount _ => rw [inc];exact inside _ _ 3 incidentArea (by decide)
  | digitWidth _ => rw [sh];exact inside _ _ 4 gridArea (by decide)
  | kindCount _ => rw [sh];exact inside _ _ ck.toNat gridArea (by cases ck <;> decide)

theorem IncidenceRead.gather (read : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (absent : j≠winner) (room : IncidenceRoom u node kernelPtr incidentPtr)
    (powers : 2^f.parties<2^W₀) (two : 2<2^W₀)
    (tempZone : ∀ a,readZone u a→a<(Aⱼ).temp ∨ (Aⱼ).temp+(fields (W:=W₀) Aⱼ).length≤a) :
    ¬partyActive Aⱼ mem ∧ MaskRoom Aⱼ mem (Aⱼ).temp ((Aⱼ).temp+(fields (W:=W₀) Aⱼ).length) := by
  have fit : (HistoryNodePorts.id (Aⱼ).nodePorts).Fits W₀ (fun _=>0) (numeric mem) (fun _=>0):=
    ⟨⟨trivial,room.cursor⟩,trivial,(mem (base u 18)).isLt,by change 1<2^W₀;omega⟩
  have v := Formula.value_eq_natural (HistoryNodePorts.id (Aⱼ).nodePorts) (fun _=>0) (numeric mem) (fun _=>0) fit
  rw [word_numeric] at v
  have idx : (HistoryNodePorts.id (Aⱼ).nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W₀):=by
    exact v.trans (congrArg (fun k : ℕ => (k : Word W₀)) read.cursor)
  have nd : nodeWord Aⱼ mem=((base u 44+8*node : ℕ):Word W₀):=by
    change (base u 44:Word W₀)+8*((HistoryNodePorts.id (Aⱼ).nodePorts).value (fun _=>0) mem (fun _=>0))=_
    simp only [idx,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have plus (q t:ℕ) (h:q+t<2^W₀) : ((q:Word W₀)+(t:Word W₀)).val=q+t:=by
    rw [←Nat.cast_add,Fin.val_cast_of_lt h]
  have atNode : (nodeWord Aⱼ mem+5).val=nodePtr+5:=by
    rw [nd]
    simpa only [Nat.cast_ofNat] using plus (base u 44+8*node) 5 room.node
  have ker : (selected Aⱼ mem).kernel=(kernelPtr:Word W₀):=by
    change mem (nodeWord Aⱼ mem+5).val=_;rw [atNode]
    apply Fin.ext
    exact read.kernel.trans (Fin.val_cast_of_lt (by have:=room.kernel;omega)).symm
  have get (t:ℕ) (h:kernelPtr+t<2^W₀) :
      ((selected Aⱼ mem).kernel+(t:Word W₀)).val=kernelPtr+t:=by rw [ker];exact plus _ _ h
  have incAt : ((selected Aⱼ mem).kernel+4).val=kernelPtr+4 := by
    simpa only [Nat.cast_ofNat] using get 4 room.kernel
  have countAt : ((selected Aⱼ mem).kernel+3).val=kernelPtr+3 := by
    simpa only [Nat.cast_ofNat] using get 3 (by have:=room.kernel;omega)
  have inc : (selected Aⱼ mem).incident=(incidentPtr:Word W₀):=by
    change mem ((selected Aⱼ mem).kernel+4).val+(6*0:ℕ)=_
    rw [incAt];simp only [Nat.mul_zero,Nat.cast_zero,add_zero]
    apply Fin.ext;exact read.incident.trans (Fin.val_cast_of_lt (by have:=room.incident;omega)).symm
  have mx : ((selected Aⱼ mem).incident+5).val=incidentPtr+5:=by rw [inc];exact plus _ 5 room.incident
  have one : 0<(wordAt mem (selected Aⱼ mem).kernel 3).val:=by
    change 0<(mem ((selected Aⱼ mem).kernel+3).val).val;rw [countAt];exact read.count
  have mask : (wordAt mem (selected Aⱼ mem).incident 5).val=2^winner.val:=by
    change (mem ((selected Aⱼ mem).incident+5).val).val=_;rw [mx];exact read.mask
  refine ⟨fun h=>absent ((gather_occupied A mem winner j one mask powers two).mp h),?_⟩
  have cursorVal : (((Aⱼ).nodePorts.cursor:Word W₀)).val = base u 18 := Fin.val_cast_of_lt room.cursor
  exact ⟨by rw [cursorVal];exact tempZone _ (.inr le_rfl),
    by rw [atNode];exact tempZone _ room.nodeArea,by rw [countAt];exact tempZone _ room.kernelCount,
    fun _=>by rw [incAt];exact tempZone _ room.kernelPtr,fun _=>by rw [mx];exact tempZone _ room.incidentMask⟩

section DormantParty
variable (g actual maskVal:ℕ)
local notation "Dⱼ" => rawParty A g j.val
local notation "DJ" => (Dⱼ).party
local notation "record" => incidentPtr+6*g

/-- When the motif ordinal is past the selected header's count, neither the incident pointer
nor a mask word is read. For an in-range motif, only this party's bit must be zero. -/
structure DormantRead (rawParty : ℕ) : Prop where
  cursor : numeric mem (base u 18)-1=node
  kernel : numeric mem (nodePtr+5)=kernelPtr
  count : numeric mem (kernelPtr+3)=actual
  incident : g<actual→numeric mem (kernelPtr+4)=incidentPtr
  mask : g<actual→numeric mem (record+5)=maskVal
  off : g<actual→maskVal.testBit rawParty=false

structure DormantRoom : Prop where
  cursor : base u 18<2^W₀
  node : nodePtr+5<2^W₀
  count : kernelPtr+3<2^W₀
  nodeArea : readZone u (nodePtr+5)
  countArea : readZone u (kernelPtr+3)
  pointer : g<actual→kernelPtr+4<2^W₀ ∧ readZone u (kernelPtr+4)
  row : g<actual→ record+5<2^W₀ ∧ readZone u (record+5)

local notation "IdleRead" => fun μ=>DormantRead u node μ kernelPtr incidentPtr g actual maskVal j.val
local notation "IdleRoom" => DormantRoom u node kernelPtr incidentPtr g actual

theorem DormantRead.retain {before after:Memory W₀} (read:IdleRead before) (r:IdleRoom)
    (frame:∀ x,readZone u x→after x=before x) : IdleRead after:=by
  have eq (x) (h:readZone u x) : numeric after x=numeric before x:=congrArg Fin.val (frame x h)
  exact ⟨by rw [eq (base u 18) (.inr le_rfl)];exact read.cursor,
    (eq _ r.nodeArea).trans read.kernel,(eq _ r.countArea).trans read.count,
    fun h=>(eq _ (r.pointer h).2).trans (read.incident h),fun h=>(eq _ (r.row h).2).trans (read.mask h),read.off⟩

theorem DormantRead.seed (read:IdleRead mem) (r:IdleRoom) (ck:Bool) :
    ¬occupied DJ (numeric mem) ∧ ∀ x,HistoryPartyBootExec.SeedRead DJ ck (numeric mem) x→ readZone u x ∧ x<2^W₀:=by
  have ker : HistoryPartyBatch.kernel DJ (numeric mem)=kernelPtr:=by
    change numeric mem (base u 44+8*(numeric mem (base u 18)-1)+5)=_;rw [read.cursor,read.kernel]
  have one : numeric mem (HistoryPartyBatch.kernel DJ (numeric mem)+3)=actual:=by rw [ker];exact read.count
  have inc (h:g<actual) : HistoryPartyBatch.incident DJ (numeric mem)=record:=by
    change numeric mem (HistoryPartyBatch.kernel DJ (numeric mem)+4)+6*g=_
    rw [ker,read.incident h]
  have off : ¬occupied DJ (numeric mem):=by
    rintro ⟨hi,bit⟩
    have pos : g<actual:=by change g<numeric mem (HistoryPartyBatch.kernel DJ (numeric mem)+3) at hi;simpa only [one] using hi
    change numeric mem (HistoryPartyBatch.incident DJ (numeric mem)+5)/2^j.val%2=1 at bit
    rw [inc pos,read.mask pos] at bit
    have zero:=read.off pos;simp [Nat.testBit_eq_decide_div_mod_eq,bit] at zero
  refine ⟨off,?_⟩
  intro x probe
  cases probe with
  | cursor => exact ⟨.inr le_rfl,r.cursor⟩
  | node =>
    change readZone u (base u 44+8*(numeric mem (base u 18)-1)+5) ∧
      base u 44+8*(numeric mem (base u 18)-1)+5<2^W₀
    rw [read.cursor]
    exact ⟨r.nodeArea,r.node⟩
  | motifCount => rw [ker];exact ⟨r.countArea,r.count⟩
  | incidentPtr hi =>
    change g<numeric mem (HistoryPartyBatch.kernel DJ (numeric mem)+3) at hi
    rw [ker];have pos:g<actual:=by simpa only [one] using hi
    exact ⟨(r.pointer pos).2,(r.pointer pos).1⟩
  | partyMask hi =>
    change g<numeric mem (HistoryPartyBatch.kernel DJ (numeric mem)+3) at hi
    have pos:g<actual:=by simpa only [one] using hi
    rw [inc pos];exact ⟨(r.row pos).2,(r.row pos).1⟩
  | kindIndex h => exact (off h).elim
  | copyCount h => exact (off h).elim
  | digitWidth h => exact (off h).elim
  | kindCount h => exact (off h).elim

theorem DormantRead.gather (read:IdleRead mem) (r:IdleRoom)
    (motif:g<2^W₀) (power:2^f.parties<2^W₀) (two:2<2^W₀)
    (tempZone:∀ x,readZone u x→x<(Dⱼ).temp ∨ (Dⱼ).temp+(fields (W:=W₀) Dⱼ).length≤x) :
    ¬partyActive Dⱼ mem ∧ MaskRoom Dⱼ mem (Dⱼ).temp ((Dⱼ).temp+(fields (W:=W₀) Dⱼ).length) := by
  have fit : (HistoryNodePorts.id (Dⱼ).nodePorts).Fits W₀ (fun _=>0) (numeric mem) (fun _=>0):=
    ⟨⟨trivial,r.cursor⟩,trivial,(mem (base u 18)).isLt,by change 1<2^W₀;omega⟩
  have val:=Formula.value_eq_natural (HistoryNodePorts.id (Dⱼ).nodePorts) (fun _=>0) (numeric mem) (fun _=>0) fit
  rw [word_numeric] at val
  have idx : (HistoryNodePorts.id (Dⱼ).nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W₀):=
    val.trans (congrArg (fun n : ℕ => (n : Word W₀)) read.cursor)
  have nd:nodeWord Dⱼ mem=((nodePtr:ℕ):Word W₀):=by
    change (base u 44:Word W₀)+8*((HistoryNodePorts.id (Dⱼ).nodePorts).value (fun _=>0) mem (fun _=>0))=_
    simp only [idx,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have plus (q t:ℕ) (h:q+t<2^W₀):((q:Word W₀)+(t:Word W₀)).val=q+t:=by rw [←Nat.cast_add,Fin.val_cast_of_lt h]
  have atNode:(nodeWord Dⱼ mem+5).val=nodePtr+5:=by rw [nd];exact plus _ 5 r.node
  have ker:(selected Dⱼ mem).kernel=(kernelPtr:Word W₀):=by
    change mem (nodeWord Dⱼ mem+5).val=_;rw [atNode]
    apply Fin.ext;exact read.kernel.trans (Fin.val_cast_of_lt (by have:=r.count;omega)).symm
  have cnt:((selected Dⱼ mem).kernel+3).val=kernelPtr+3:=by rw [ker];exact plus _ 3 r.count
  have size:(wordAt mem (selected Dⱼ mem).kernel 3).val=actual:=by
    change numeric mem ((selected Dⱼ mem).kernel+3).val=actual;rw [cnt,read.count]
  have lk (h:g<actual):((selected Dⱼ mem).kernel+4).val=kernelPtr+4:=by rw [ker];exact plus _ 4 (r.pointer h).1
  have inc (h:g<actual):(selected Dⱼ mem).incident=((record:ℕ):Word W₀):=by
    change mem ((selected Dⱼ mem).kernel+4).val+((6*g:ℕ):Word W₀)=_
    rw [lk h,Nat.cast_add]
    congr 1
    apply Fin.ext;exact (read.incident h).trans (Fin.val_cast_of_lt (by have:=(r.row h).1;omega)).symm
  have mx (h:g<actual):((selected Dⱼ mem).incident+5).val=record+5:=by rw [inc h];exact plus _ 5 (r.row h).1
  have norm (h:((Dⱼ).party.motif:Word W₀)<wordAt mem (selected Dⱼ mem).kernel 3) : g<actual:=by
    change ((g:Word W₀)).val<(wordAt mem (selected Dⱼ mem).kernel 3).val at h
    simpa only [Fin.val_cast_of_lt motif,size] using h
  constructor
  · rw [HistoryGatherBody.partyActive_iff _ _ motif ((Nat.pow_le_pow_right (by decide : 0<2) j.isLt.le).trans_lt power) two]
    rintro ⟨hi,bit⟩
    change g<(wordAt mem (selected Dⱼ mem).kernel 3).val at hi
    have pos:g<actual:=by simpa only [size] using hi
    change (numeric mem ((selected Dⱼ mem).incident+5).val).testBit j.val=true at bit
    rw [mx pos,read.mask pos,read.off pos] at bit;contradiction
  · refine ⟨?_,?_,?_,?_,?_⟩
    · change ((base u 18:ℕ):Word W₀).val<_ ∨ _≤((base u 18:ℕ):Word W₀).val
      rw [Fin.val_cast_of_lt r.cursor]
      exact tempZone _ (.inr le_rfl)
    · rw [atNode];exact tempZone _ r.nodeArea
    · rw [cnt];exact tempZone _ r.countArea
    · intro hi;rw [lk (norm hi)];exact tempZone _ (r.pointer (norm hi)).2
    · intro hi;rw [mx (norm hi)];exact tempZone _ (r.row (norm hi)).2

omit [CommRing F] in
/-- Starting from a single raw S44 row and the two incidence pointers, run both
vacant batches, their zero-length pair, and the gather header. The five incidence
reads are recovered across every intermediate physical state below. -/
theorem physical_dormant_room (id : ((Fin 3→Bool)→F)→ℕ)
    (read : IdleRead mem)
    (immutable : IdleRoom)
    (age : 16≤u) (count : node<V^2) (motifs : g<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (headerCap : 3+5*f.demands+4*f.supplies≤V)
    (ports : HistoryGatherExecution.portsEnd Dⱼ<2^W₀) :
    VacantRoom Dⱼ node id mem ∧ ∀ x,(readZone u x ∨ OutsideNode u node x)→vacantPass Dⱼ node id mem x=mem x := by
  let X:=vacantChecks DJ mem
  let Y:=vacantPayload DJ mem
  let P:=HistoryPartyPairExec.build DJ node 0 0 (Y.published [])
  let sp:=afterVacantPair DJ node id mem
  let loc:=fun k:ℕ=>(⟨g+2,j.val+2,k,1⟩:Local)
  let page:=fun k=>atWord (base u 12) V f.motifs f.parties node (loc k) 0
  have ok (k:ℕ) (h:k<8) : (loc k).Valid f.motifs f.parties:=
    by
      change g+2<f.motifs+2 ∧ j.val+2<f.parties+2 ∧ k<8 ∧ 1<32
      exact ⟨Nat.add_lt_add_right motifs 2,Nat.add_lt_add_right j.isLt 2,h,by decide⟩
  have reg (k:ℕ) (h:k<8) : base u 12≤page k ∧ page k+V≤base u 12+Diagonal.TickWorkspace.stride u :=
    ⟨(local_window u f node age count capacity _ (ok k h)).1,(local_window u f node age count capacity _ (ok k h)).2.1⟩
  have v₁ : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have grow : 10*V≤V^4:=calc
    _≤V*V:=Nat.mul_le_mul_right _ (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have s12:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<14)
  have s14:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 14<15)
  have s15:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 15<16)
  have s16:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 16<17)
  have s17:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 17<18)
  have wide:=immutable.cursor
  change base u 14+V^4≤base u 15 at s14
  change base u 15+V^4≤base u 16 at s15
  change base u 16+V^4≤base u 17 at s16
  change base u 17+V^4≤base u 18 at s17
  let zone := fun x => readZone u x ∨ OutsideNode u node x
  have large (x:ℕ) (z:zone x):x<base u 14 ∨ base u 18≤x:=by
    rcases z with (h|h)|h
    · omega
    · exact Or.inr h
    · have s19:=Diagonal.TickWorkspace.apart (u:=u) (by decide : 18<19)
      have sh:=h.scratch
      omega
  have zseed (x:ℕ) (z:readZone u x) : x<base u 14+V ∨ base u 14+V+37≤x:=by
    rcases z with h|h <;> omega
  have ztemp (x:ℕ) (z:zone x) : x<(Dⱼ).temp ∨ (Dⱼ).temp+(fields (W:=W₀) Dⱼ).length≤x:=by
    rw [HistoryGatherExecution.header_size]
    change x<base u 17 ∨ base u 17+(3+5*f.demands+4*f.supplies)≤x
    have h:=large x z;omega
  have zpage (k x:ℕ) (h:k<8) (z:zone x) : x<page k ∨ page k+4≤x:=by
    rcases z with (h₁|h₂)|outside
    · have p:=reg k h;omega
    · have p:=reg k h;omega
    · exact outside.private_range capacity (loc k) (ok k h) 4 (by omega)
  have source (m:Memory W₀) (r:IdleRead m) (ck:Bool) :
      (⟨DJ,ck,emptyKind,m⟩:HistoryPartyBatchExec.Build W₀).Source [] ∧ ¬occupied DJ (numeric m):=by
    have h:=DormantRead.seed u arch f node j m kernelPtr incidentPtr g actual maskVal r immutable ck
    exact ⟨physical_vacant_source_at u arch f node g j ck m age count motifs capacity r.cursor h.1
      (fun a x=>⟨zseed a (h.2 a x).1,(h.2 a x).2⟩) mask lookup lutStride pages pageStride counts lutAway countsAway,h.1⟩
  have batch (Z:HistoryPartyBatchExec.Build W₀) (same : Z.layout=DJ) (off : ¬occupied DJ (numeric Z.input))
      (x:ℕ) (outside : x<base u 14 ∨ base u 18≤x) (rootOff : x<Z.target ∨ Z.target+4≤x) : BatchAway Z [] x:=by
    have eq : Z.count=0:=by
      simp [HistoryPartyBatchExec.Build.count,same,children,HistoryPartyBatch.copies,kinds,off]
    have cur : Z.ctrl.val=base u 14+V+33:=by
      change ((Z.layout.seed+33:ℕ):Word W₀).val=_
      rw [same];exact Fin.val_cast_of_lt (by change base u 14+V+33<_;omega)
    refine ⟨by rw [cur];omega,?_,?_,?_,?_,by simp,rootOff⟩ <;> rw [same]
    · change x<base u 14+V ∨ base u 14+V+37≤x;omega
    · change x<base u 14+2*V ∨ base u 14+2*V+26≤x;omega
    · rw [eq];change x<base u 15 ∨ base u 15+21*0≤x;omega
    · rw [eq];change x<base u 16 ∨ base u 16+23*0≤x;omega
  have check:=source mem read true
  have atX : X.target=page 1:=by change dest DJ true (numeric mem (base u 18)-1) 1=_;rw [read.cursor];rfl
  have xaway (x:ℕ) (z:zone x) : BatchAway X [] x:=
    batch X rfl check.2 x (large x z) (by rw [atX];exact zpage 1 x (by decide) z)
  have first (x:ℕ) (z:readZone u x) : X.published [] x=mem x:=(xaway x (.inl z)).keeps check.1.seedRoom
  have retain {before after : Memory W₀} (r : IdleRead before)
      (frame : ∀ x,readZone u x→after x=before x) : IdleRead after :=
    DormantRead.retain u f node j kernelPtr incidentPtr g actual maskVal r immutable frame
  have readC:=retain read first
  have payload:=source (X.published []) readC false
  have atY : Y.target=page 0:=by change dest DJ false (numeric (X.published []) (base u 18)-1) 1=_;rw [readC.cursor];rfl
  have yaway (x:ℕ) (z:zone x) : BatchAway Y [] x:=
    batch Y rfl payload.2 x (large x z) (by rw [atY];exact zpage 0 x (by decide) z)
  have second (x:ℕ) (z:readZone u x) : Y.published [] x=X.published [] x:=(yaway x (.inl z)).keeps payload.1.seedRoom
  have readP:=retain readC second
  have pairRoom:=physical_pair_room_at u arch f node g j (nullTree F) (nullTree F) id (Y.published [])
    age count motifs capacity (by omega) (by simp only [null_rows,Nat.add_zero,Nat.mul_zero,Nat.zero_le])
    (by simp only [null_bits,Nat.add_zero];exact Nat.two_pow_pos _)
    (fun i k t=>by have hk:=k.isLt;fin_cases i <;> change k.val<(nullTree F).compile.cells at hk <;>
      rw [compiled_rows,null_rows] at hk <;> omega) readP.cursor
  have saved (t:Fin 4) : BatchAway Y [] (dest DJ true node 1+t.val):=by
    have sep:=local_apart (base:=base u 12) (n:=node) (Nat.two_pow_pos _) capacity (ok 1 (by decide)) (ok 0 (by decide))
      (fun e=>by have h:=congrArg Local.family e;change (1:ℕ)=0 at h;omega)
    change page 1+V≤page 0 ∨ page 0+V≤page 1 at sep
    have cover:=reg 1 (by decide);have ht:=t.isLt
    change BatchAway Y [] (page 1+t.val)
    apply batch Y rfl payload.2 _ (.inl (by omega));rw [atY];omega
  have px : P.outputBase=page 2:=by
    have at6 : HistoryPartyPair.word DJ (numeric (Y.published [])) 6=page 2:=by
      change HistoryPartyPair.atPair DJ (numeric (Y.published []) (base u 18)-1) 1=_
      rw [readP.cursor];rfl
    have cap : page 2<2^W₀:=pairRoom.cap 6
    change (HistoryPartyPairExec.prepared DJ (Y.published []) (HistoryPartyPair.hub DJ+6)).val=_
    have savedWord : HistoryPartyPairExec.prepared DJ (Y.published []) (HistoryPartyPair.hub DJ+6) =
        (HistoryPartyPair.word DJ (numeric (Y.published [])) 6 : Word W₀) :=
      HistoryPartyPairExec.hub_read DJ (Y.published []) 6
    rw [savedWord,at6,Fin.val_cast_of_lt cap]
  have pr (x:ℕ) (z:zone x) : HistoryPartyPairExec.Retained DJ node (nullTree F) (nullTree F) id (Y.published []) x:=by
    have h:=large x z
    have ctrl : P.control.val=base u 14+V+7:=by
      change ((base u 14+V+7:ℕ):Word W₀).val=base u 14+V+7
      exact Fin.val_cast_of_lt (by omega)
    refine ⟨by change x<base u 14+V ∨ base u 14+V+9≤x;omega,
      by change x<base u 15 ∨ base u 15+28≤x;omega,by change x<base u 16 ∨ base u 16+14≤x;omega,
      by change x≠P.control.val;rw [ctrl];omega,?_⟩
    intro b hb
    have zero:=empty_pair_jobs Dⱼ node id b hb
    simp only [HistoryReadyTape.Job.finish,zero,Nat.add_zero];omega
  have hf (x:ℕ) (z:zone x) : x<HistoryPartyPair.hub DJ ∨ HistoryPartyPair.hub DJ+25≤x:=by
    have h:=large x z;change x<base u 14+V+64 ∨ base u 14+V+64+25≤x;omega
  have rootFree (x:ℕ) (z:zone x) : x<P.outputBase ∨ P.outputBase+4≤x:=by rw [px];exact zpage 2 x (by decide) z
  have keep (x:ℕ) (z:zone x) : sp x=mem x:=vacant_pair_keeps DJ node id mem x
    check.1.seedRoom (xaway x z) (yaway x z) (pr x z) (hf x z) (rootFree x z)
  have after : IdleRead sp:=retain read (fun a h=>keep a (.inl h))
  have gfit:g<2^W₀:=by have h:=Nat.le_mul_of_pos_right (f.motifs+2) (by omega : 0<f.parties+2);omega
  have gh:=DormantRead.gather u arch f node j sp kernelPtr incidentPtr g actual maskVal after immutable gfit mask (by omega) (fun a h=>ztemp a (.inl h))
  refine ⟨⟨check.1,payload.1,check.2,payload.2,read.cursor,readC.cursor,saved,pairRoom,gh.1,headerCap,ports,gh.2⟩,?_⟩
  intro x z
  exact vacant_keeps Dⱼ node id mem x (ztemp x z) check.1.seedRoom (xaway x z) (yaway x z) (pr x z) (hf x z) (rootFree x z)

end DormantParty

omit [CommRing F] in
theorem physical_vacant_room_all (id : ((Fin 3→Bool)→F)→ℕ)
    (read : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (immutable : IncidenceRoom u node kernelPtr incidentPtr) (absent : j≠winner)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (headerCap : 3+5*f.demands+4*f.supplies≤V)
    (ports : HistoryGatherExecution.portsEnd Aⱼ<2^W₀) :
    VacantRoom Aⱼ node id mem ∧ ∀ x,(readZone u x ∨ OutsideNode u node x)→vacantPass Aⱼ node id mem x=mem x := by
  let n:=numeric mem (kernelPtr+3)
  have empty : DormantRead u node mem kernelPtr incidentPtr 0 n (2^winner.val) j.val:=
    ⟨read.cursor,read.kernel,rfl,fun _=>read.incident,fun _=>read.mask,
      fun _=>by rw [Nat.testBit_two_pow];simpa using (show winner.val≠j.val from fun h=>absent (Fin.ext h.symm))⟩
  have room : DormantRoom u node kernelPtr incidentPtr 0 n:=
    ⟨immutable.cursor,immutable.node,by have:=immutable.kernel;omega,immutable.nodeArea,immutable.kernelCount,
      fun _=>⟨immutable.kernel,immutable.kernelPtr⟩,fun _=>⟨immutable.incident,immutable.incidentMask⟩⟩
  exact physical_dormant_room u arch f node j mem kernelPtr incidentPtr 0 n (2^winner.val) id empty room
    age count motifs capacity mask lookup lutStride pages pageStride counts lutAway countsAway headerCap ports

omit [CommRing F] in
theorem physical_vacant_room (id : ((Fin 3→Bool)→F)→ℕ)
    (read : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (immutable : IncidenceRoom u node kernelPtr incidentPtr) (absent : j≠winner)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (headerCap : 3+5*f.demands+4*f.supplies≤V)
    (ports : HistoryGatherExecution.portsEnd Aⱼ<2^W₀) :
    VacantRoom Aⱼ node id mem ∧ ∀ x,readZone u x→vacantPass Aⱼ node id mem x=mem x  := by
  have h:=physical_vacant_room_all u arch f node winner j mem kernelPtr incidentPtr id read immutable absent age count motifs capacity mask lookup lutStride pages pageStride counts lutAway countsAway headerCap ports
  exact ⟨h.1,fun x hx=>h.2 x (.inl hx)⟩

end Incidence

end PhysicalOrder


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
