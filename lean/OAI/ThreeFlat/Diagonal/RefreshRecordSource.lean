import OAI.ThreeFlat.Diagonal.RefreshRecordRows
import OAI.ThreeFlat.Diagonal.RefreshSparseImage

namespace OAI
/-! # Native four-table recorder from a retained successor image and choice words -/

namespace ThreeFlat.Diagonal.RefreshStageNav.Records

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.DescriptorExpr RAM.HeaderScan
open RAM.PhysicalPinsExpr RAM.MotifRows RefreshDemandRows CompressorPacking.Native
open scoped Classical Fin.CommRing

variable {W v m d t : ℕ} {cur : Word W} {mem : Memory W}
open private memoryValues from OAI.ThreeFlat.Diagonal.RefreshRecordNative

structure Data (cur : Word W) (mem : Memory W) (head : ℕ) (P : Pointers) (C : SlotImage.Columns)
    (G : LiftedSlots (Fin v × Fin m) d (BitWord t)) (w : SlotImage.Edge (Fin v × Fin m) (BitWord t) d→ℕ)
    (read : ℕ→ℕ) : Prop where
  pointer : (mem cur.val).val=head
  header : head+41<2^W
  table (q : Table) : info (fun i=>(mem i).val) cur q.start=P.dst q
  span (q : Table) : info (fun i=>(mem i).val) cur (q.start+1)=v*m*2^t*q.cols d
  dense : info (fun i=>(mem i).val) cur 1=P.counts
  desc : info (fun i=>(mem i).val) cur 2=P.choices
  lanes : info (fun i=>(mem i).val) cur 8=2^t
  graph : info (fun i=>(mem i).val) cur 14=C.graph
  rows : info (fun i=>(mem i).val) cur 15=C.rows
  width : info (fun i=>(mem i).val) cur 19=C.widths
  image : SlotImage.Stored G finProdFinEquiv (tagOrdinal t) C (fun i=>(mem i).val) w
  choice : ∀ i,P.choices≤ i → i<P.choices+3*(v*2^t) → (mem i).val=read i

variable {G : LiftedSlots (Fin v × Fin m) d (BitWord t)} {w : SlotImage.Edge (Fin v × Fin m) (BitWord t) d→ℕ}
variable {head : ℕ} {P : Pointers} {C : SlotImage.Columns} {read : ℕ→ℕ}

def inputs (cur head : ℕ) (P : Pointers) (C : SlotImage.Columns) (v m t d i : ℕ) :=
  i=cur ∨ head≤ i ∧ i≤head+41 ∨ P.choices≤ i ∧ i<P.choices+3*(v*2^t) ∨
  C.graph≤ i ∧ i<C.graph+6*C.rows ∨ C.widths≤ i ∧ i<C.widths+v*m*d*2^t

theorem Data.frame (s : Data cur mem head P C G w read) (out : Memory W)
    (keep : ∀ i,inputs cur.val head P C v m t d i → out i=mem i) : Data cur out head P C G w read := by
  have ptr := keep cur.val (.inl rfl)
  have keepH (j : ℕ) (hj : j≤41) : info (fun i=>(out i).val) cur j=info (fun i=>(mem i).val) cur j :=
    info_frame cur mem 41 (fun i hi=>keep i (by rw [s.pointer] at hi; exact hi.imp_right Or.inl)) j hj
  refine ⟨(congrArg Fin.val ptr).trans s.pointer,s.header,?_,?_,(keepH 1 (by decide)).trans s.dense,
    (keepH 2 (by decide)).trans s.desc,(keepH 8 (by decide)).trans s.lanes,
    (keepH 14 (by decide)).trans s.graph,(keepH 15 (by decide)).trans s.rows,(keepH 19 (by decide)).trans s.width,?_,?_⟩
  · intro q
    exact (keepH _ (by cases q <;> decide)).trans (s.table q)
  · intro q
    exact (keepH _ (by cases q <;> decide)).trans (s.span q)
  · apply s.image.frame
    · exact fun i ha hb=>congrArg Fin.val (keep i (.inr (.inr (.inr (.inl ⟨ha,hb⟩)))))
    · exact fun i ha hb=>congrArg Fin.val (keep i (.inr (.inr (.inr (.inr ⟨ha,hb⟩)))))
  · exact fun i ha hb => (congrArg Fin.val (keep i (.inr (.inr (.inl ⟨ha,hb⟩))))).trans (s.choice i ha hb)

structure Limits (W v m t d : ℕ) (P : Pointers) (C : SlotImage.Columns) : Prop where
  small : 6<2^W
  ports : m<2^W
  degree : 2*d<2^W
  lanes : 2^t<2^W
  choices : P.choices+3*(v*2^t)≤2^W
  graph : C.graph+6*C.rows≤2^W
  widths : C.widths+v*m*d*2^t≤2^W

theorem Table.native (s : Data cur mem head P C G w read) (lim : Limits W v m t d P C)
    (K : ℕ) (q : Table) (r : Site v m t × Fin (q.cols d)) (addr : Word W)
    (pos : addr.val=P.dst q+(rowOrder d q r).val) :
    (q.expression cur m d K).eval Fin.elim0 mem (fun _=>addr)=(q.value P head K G w read r:Word W) := by
  obtain ⟨u,f⟩ := r
  have hd : (mem cur.val).val+40<2^W := by rw [s.pointer]; have := s.header; omega
  let z : Block v t := (u.1.1,u.2)
  let pt := u.1.2
  have key : (rowOrder d q (u,f)).val=siteId z pt*q.cols d+f.val := by
    rw [rowOrder,RefreshStageLayout.pair_index,siteOrder_val]
    rfl
  rw [key] at pos
  have dstKernel : info (memoryValues mem) cur 34=P.kernel := s.table .kernel
  have dstMotif : info (memoryValues mem) cur 36=P.motif := s.table .motif
  have dstHeader : info (memoryValues mem) cur 38=P.headers := s.table .halfHeader
  have dstHalves : info (memoryValues mem) cur 40=P.halves := s.table .halves
  cases q with
  | kernel =>
    have a := kernel_native cur mem (fun _=>addr) (siteId z pt) f hd lim.small (by simpa only [dstKernel, Pointers.dst, Table.cols, Nat.add_assoc] using pos)
    simpa only [Table.expression,Table.value,s.pointer,dstMotif] using a
  | motif =>
    have hz := (RefreshStageLayout.blocks z).isLt
    rw [RefreshStageLayout.block_index] at hz
    have limC := lim.choices
    have plus : P.choices+blockId z*3+1<P.choices+3*(v*2^t) := by omega
    have below : P.choices+blockId z*3<P.choices+3*(v*2^t) := by omega
    have counts : info (memoryValues mem) cur 1=P.counts := s.dense
    have choices : info (memoryValues mem) cur 2=P.choices := s.desc
    have plusRead : memoryValues mem (P.choices+blockId z*3+1)=_ := s.choice _ (by omega) plus
    have belowRead : memoryValues mem (P.choices+blockId z*3)=_ := s.choice _ (by omega) below
    have a := motif_native cur mem (fun _=>addr) K z pt f hd lim.small lim.ports s.lanes
      (by simpa only [dstMotif, Pointers.dst, Table.cols, Nat.add_assoc] using pos) (by rw [choices]; omega)
    simpa only [Table.expression,Table.value,counts,choices,plusRead,belowRead] using a
  | halfHeader =>
    have a := halfHeader_native cur mem (fun _=>addr) d (siteId z pt) f hd lim.small (by simpa only [dstHeader, Pointers.dst, Table.cols, Nat.add_assoc] using pos)
    simpa only [Table.expression,Table.value,dstHalves] using a
  | halves =>
    obtain ⟨⟨j,f⟩,rfl⟩ := halfCol.surjective f
    have site : ShrinkStage.Halves.siteNumber finProdFinEquiv u=siteId z pt := by
      change (u.1.2.val+m*u.1.1.val)*2^t+(tagOrdinal t u.2).val =
        (u.1.1.val*m+u.1.2.val)*2^t+(tagOrdinal t u.2).val
      ac_rfl
    have a := halves_native cur mem (fun _=>addr) G finProdFinEquiv C w s.image u j f hd
      (by have := lim.small; omega) lim.degree lim.lanes s.lanes s.graph s.rows s.width lim.graph lim.widths (by
        rw [dstHalves,site]
        rw [halfCol_val] at pos
        change addr.val=P.halves+(siteId z pt*(8*d)+(j.val*4+f.val)) at pos
        rw [pos]
        ring)
    simpa only [Table.expression,Table.value,Equiv.symm_apply_apply] using a

end ThreeFlat.Diagonal.RefreshStageNav.Records

end OAI
