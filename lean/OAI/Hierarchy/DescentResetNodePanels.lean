import OAI.Hierarchy.DescentResetLocalNodes
import OAI.Hierarchy.DescentPackedLocalLookup
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native gathering of prior node and operand fields in the installed reset's local order -/
namespace Hierarchy.DescentResetNodePanels
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Gather DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedFallbackTree.Image ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D K b hosts groups M w cap : ℕ}

/-- Each donor supplies its genuine node count and one fixed field of its previous local node/operand panel. -/
abbrev Shelves (D K b : ℕ) := Fin D→Fin (K+1)→Cell b
def count (a : Shelves D K b) (d : Fin D) := (a d 0).val
def start (a : Shelves D K b) := ProtocolRAMPortRanks.«prefix» (count a) (fun q=>q.val)

def contribution (a : Shelves D K b) (q : Fin D) (t : ℕ) : ℕ :=
  if ok : start a q≤t ∧ t<start a q+count a q ∧ t-start a q<K then
    (a q (Fin.succ ⟨t-start a q,ok.2.2⟩)).val else 0

def packed (a : Shelves D K b) (cap : ℕ) : Cell (b*cap) :=
  encode b cap (fun t=>⟨(∑q,contribution a q t.val)%2^b,Nat.mod_lt _ (Nat.two_pow_pos _)⟩)

theorem packed_read (a : Shelves D K b) (cap : ℕ) (q : Fin D) (j : Fin K) (live : j.val<count a q)
    (room : start a q+j.val<cap) :
    digit b (start a q+j.val) (packed a cap).val=(a q j.succ).val := by
  let t : Fin cap:=⟨start a q+j.val,room⟩
  have pick : ∑i,contribution a i t.val=(a q j.succ).val := by
    rw [Finset.sum_eq_single q]
    · simp [contribution,t,live,j.isLt]
    · intro i _ ne
      by_cases less : i.val<q.val
      · have before:=ProtocolRAMPortRanks.prefix_disjoint (count a) (fun n=>n.val) less
        change start a i+count a i≤ start a q at before
        simp [contribution,t,show ¬start a q+j.val<start a i+count a i by omega]
      · have lt : q.val < i.val := by have neq : i.val≠q.val:=fun x=>ne (Fin.ext x);omega
        have after:=ProtocolRAMPortRanks.prefix_disjoint (count a) (fun n=>n.val) lt
        change start a q+count a q≤ start a i at after
        simp [contribution,t,show ¬start a i≤ start a q+j.val by omega]
    · simp
  change digit b t.val (packed a cap).val=_
  unfold packed
  rw [digit_encode]
  change (∑ i, contribution a i t.val) % 2^b = (a q j.succ).val
  exact (congrArg (fun z => z % 2^b) pick).trans (Nat.mod_eq_of_lt (a q j.succ).isLt)

def raw (a : Shelves D K b) := encode (b*(K+1)) D (fun d=>encode b (K+1) (a d))
def compact (D K b cap : ℕ) (x : Cell ((b*(K+1))*D)) : Cell (b*cap) :=
  packed (fun d=>(encode b (K+1)).symm ((encode (b*(K+1)) D).symm x d)) cap

@[simp] theorem compact_raw (a : Shelves D K b) (cap : ℕ) : compact D K b cap (raw a)=packed a cap := by
  simp [raw,compact]

variable {I : Type} [Fintype I] (J : I→Type) [∀i,Fintype (J i)] (ticket : I↪Fin D)
variable (prior : ∀i,J i↪ℕ)
def countsAt (d : Fin D) := ∑i : I,if ticket i=d then Fintype.card (J i) else 0

theorem count_at (i : I) : countsAt J ticket (ticket i)=Fintype.card (J i) := by
  simp [countsAt,ticket.injective.eq_iff]

theorem start_at (a : Shelves D K b) (readCount : ∀d,count a d=countsAt J ticket d) (i : I) :
    start a (ticket i) = ∑j ∈ Finset.univ.filter (fun j=>(ticket j).val<(ticket i).val),Fintype.card (J j) := by
  classical
  unfold start ProtocolRAMPortRanks.«prefix»
  simp_rw [readCount,countsAt]
  rw [Finset.sum_comm]
  calc
    _=∑x : I,if (ticket x).val<(ticket i).val then Fintype.card (J x) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : ticket x < ticket i <;> simp [Finset.sum_ite_eq, h]
    _=_ := (Finset.sum_filter ..).symm

theorem local_read (a : Shelves D K b) (field : (i:I)→J i→Cell b)
    (readCount : ∀d,count a d=countsAt J ticket d) (fits : ∀i,Fintype.card (J i)≤K)
    (oldField : ∀i u,a (ticket i) (Fin.succ ((DescentResetLocalNodes.ordinal (prior i) u).castLE (fits i)))=field i u)
    (room : Fintype.card (Σi,J i)≤cap) (i : I) (u : J i) :
    digit b (DescentResetLocalNodes.oldOrder J (ticket.trans Fin.valEmbedding) prior ⟨i,u⟩).val
      (packed a cap).val=(field i u).val := by
  let k:=DescentResetLocalNodes.ordinal (prior i) u
  have position : (DescentResetLocalNodes.oldOrder J (ticket.trans Fin.valEmbedding) prior ⟨i,u⟩).val=start a (ticket i)+k.val := by
    rw [DescentResetLocalNodes.oldOrder_val,start_at J ticket a readCount]
    exact congrArg (_+·) (DescentRosterOrder.compact_read (prior i) u).symm
  have live : k.val<count a (ticket i) := by rw [readCount,count_at];exact k.isLt
  have fit : start a (ticket i)+k.val<cap := by
    rw [←position]
    exact (DescentResetLocalNodes.oldOrder J (ticket.trans Fin.valEmbedding) prior ⟨i,u⟩).isLt.trans_le room
  rw [position,←oldField i u]
  exact packed_read a cap (ticket i) (k.castLE (fits i)) live fit

/-- Read each previous donor's local shelf from its own expression, then one packed ROM reorders every true node.
The same source theorem applies to a tag, arity, or a fixed argument column of the prior book. -/
theorem issued (T : Fin D→Tables) (field : Fin D→Expr) (g : Banks) (mid out : ℕ)
    (a : Fin hosts→Fin groups→Shelves D K b) (pos : 0<M) (mem : Memory w)
    (bounds : Bounds (w:=w) (d:=b*(K+1)) (M:=M) T field mid)
    (tables : ∀j,Static (T j) (setField (d:=b*(K+1)) j) M mem)
    (previous : ∀j,Source (field j) (fun h i=>encode b (K+1) (a h i j)) M mem)
    (space : mid+hosts*chunks groups M<2^w)
    (fit : DescentSIMDLookup.Fits g ((b*(K+1))*D) (b*cap) M hosts groups w out)
    (res : resident (compact D K b cap) g hosts groups M mem)
    (dict : g.dictionary.base+2^(((b*(K+1))*D)*M)≤ mid) (mask : g.mask.base+hosts*chunks groups M≤ mid)
    (source : g.source.base=mid) :
    let rows:=hosts*chunks groups M
    let act:=assembly T field
    let dst:=imageBank hosts groups M out g (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program g out hosts groups M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    ∀v i,digit (b*cap) (lane i pos).val (dst (out+(row hosts groups M (position v i pos)).val)).val=
      (packed (a v i) cap).val := by
  let rows:=hosts*chunks groups M
  let act:=assembly T field
  let midMem:=image mid rows act mem
  have low (z : ℕ) (below : z< mid) : midMem z=mem z:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl below)
  have live : resident (compact D K b cap) g hosts groups M midMem := by
    constructor
    · intro k
      rw [low _ (by have:=k.isLt;omega)]
      exact res.1 k
    · intro k
      rw [low _ (by have:=k.isLt;omega)]
      exact res.2 k
  have gathered:=collected T field mid bounds mem tables (fun h i j=>encode b (K+1) (a h i j)) previous (List.finRange D)
  have read (t : Row hosts groups M) : midMem (g.source.base+(row hosts groups M t).val)= ((data (fun h i=>raw (a h i)) t).val : Word w) := by
    rw [source]
    apply (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans
    simpa only [act,assembly,raw,List.mem_finRange,ite_true] using gathered t
  obtain ⟨run,reads,_,_⟩:=DescentPackedLocalLookup.compile g out (compact D K b cap)
    (fun h i=>raw (a h i)) pos fit midMem live read
  have first : (scan w mid rows act).Exec mem midMem (4+rows*(2*act.work+4)) :=
    scan_exec mid rows act mem
      (DescentPacking.PackedMatch.Local.Gather.fits T field mid bounds (List.finRange D)) space
  exact ⟨first.then run,fun v i=>by simpa only [compact_raw] using reads v i⟩

end
end Hierarchy.DescentResetNodePanels

end OAI
