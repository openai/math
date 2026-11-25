import OAI.ThreeFlat.Diagonal.ShrinkScoreScan
import OAI.ThreeFlat.Diagonal.RefreshFormulaWork
import OAI.ThreeFlat.Diagonal.RefreshDenseAddress
import OAI.ThreeFlat.Diagonal.RefreshSparseImage
import OAI.ThreeFlat.Diagonal.ShrinkCursorLayout
import OAI.ThreeFlat.Diagonal.HistogramAdmission
import OAI.ThreeFlat.Diagonal.ShrinkNavigationLocal
import OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
import OAI.ThreeFlat.Diagonal.ShrinkTableOrdinal

namespace OAI
/-! # Filling ordered fixed-stride physical shrink rows -/
namespace ThreeFlat.Diagonal.ShrinkStageNav
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.DescriptorScan
open NavigationPass RefreshStageNav
open scoped Classical Fin.CommRing
noncomputable section

variable {W M d : ℕ} (cur : Word W) (m : Memory W)

def denseOrder (M d : ℕ) : (Fin M × Fin d) ≃ Fin (d*M) :=
  (RefreshStageLayout.pair (Equiv.refl _) (Equiv.refl _)).trans (finCongr (Nat.mul_comm _ _))

theorem denseOrder_val (i : Fin M) (j : Fin d) : (denseOrder M d (i,j)).val=i.val*d+j.val :=
  RefreshStageLayout.pair_index _ _ _

def denseFill (lo : ℕ) (value : Fin M→Fin d→ℕ) (m : Memory W) : Memory W :=
  fillSegment lo (d*M) (tableWord (denseOrder M d) lo (fun z=>(value z.1 z.2:Word W))) m

theorem dense_at (lo : ℕ) (value : Fin M→Fin d→ℕ) (i : Fin M) (j : Fin d) :
    denseFill lo value m (lo+i.val*d+j.val)=(value i j:Word W) := by
  simpa only [denseFill,denseOrder_val,Nat.add_assoc] using
    scan_read m (denseOrder M d) (fun z=>(value z.1 z.2:Word W)) lo (i,j)

theorem dense_outside (lo : ℕ) (value : Fin M→Fin d→ℕ) :
    agreesOutside lo (lo+d*M) (denseFill lo value m) m :=
  fun _i hi=>segment_other m _ _ _ _ hi

theorem header_frame {alt : Memory W} {head : ℕ} {field : ℕ→ℕ} (H : Scans.Header cur m head 63 field)
    {lo n : ℕ} (outside : agreesOutside lo (lo+n) alt m)
    (atCur : cur.val<lo ∨ lo+n≤cur.val) (hdr : head+64≤lo ∨ lo+n≤head) :
    Scans.Header cur alt head 63 field :=
  ⟨by rw [outside _ atCur];exact H.pointer,H.fit,fun i hi=>by rw [outside _ (by omega)];exact H.values i hi⟩

structure RowResult (E : Execution W) (mem : Memory W) (lo : ℕ) (value : Fin M→Fin d→ℕ) (binds : ℕ) : Prop where
  fits : E.fits mem
  image : (E.run mem).2=denseFill lo value mem
  clocks : (E.run mem).1=11+d*M*(2*binds+4)

theorem run_rows (e : Formula 1) (off count : ℕ) (head : ℕ) (field : ℕ→ℕ) (H : Scans.Header cur m head 63 field)
    (hh : max off count≤63) (len : field count=d*M) (endFit : field off+d*M<2^W)
    (value : Fin M→Fin d→ℕ)
    (reads : ∀ i j (a : Word W) (alt : Memory W),a.val=field off+(i.val*d+j.val) →
      agreesOutside (field off) (field off+d*M) alt m →
      (closed e).eval Fin.elim0 alt (fun _=>a)=(value i j:Word W)) :
    RowResult (Execution.header cur off count e) m (field off) value (closed (w:=W) e).binds := by
  have hdr : (m cur.val).val+max off count<2^W := by rw [H.pointer]; have := H.fit; omega
  have ptr : info (fun i=>(m i).val) cur off=field off := by simpa [info,H.pointer] using H.values off (by omega)
  have cnt : info (fun i=>(m i).val) cur count=d*M := by simpa [info,H.pointer] using (H.values count (by omega)).trans len
  refine ⟨?_,?_,?_⟩
  · change (headerWord m cur off).val+(headerWord m cur count).val<2^W
    rw [H.get off (by omega),H.get count (by omega),len]
    exact endFit
  · apply scan_table cur m (denseOrder M d) (fun p=>(value p.1 p.2:Word W)) (closed e) off count (field off) hdr ptr cnt endFit
    intro z a alt atArg frame
    exact reads z.1 z.2 a alt (atArg.trans (by rw [denseOrder_val])) frame
  · change 11+(headerWord m cur count).val*(2*(closed (w:=W) e).binds+4)=_
    rw [H.get count (by omega),len]

open private nativeMemory nativeValue from
  OAI.ThreeFlat.Diagonal.ShrinkChoiceNative

variable {head k : ℕ} {field : ℕ→ℕ} (H : Scans.Header cur m head 63 field)

include H in
theorem choices_run (base : Fin (k+1)→Fin 2→ℕ) (size : Fin (k+1)→ℕ) (demand : Fin M→Fin 2→ℕ)
    (len : field 28=3*M) (cap : field 2+3*M<2^W) (atCur : field 2+3*M≤cur.val)
    (hdr : head+64≤field 2) (three : 3<2^W) (table : k+1≤2^W)
    (dataStart : field 2+3*M≤field 8) (dataEnd : field 8+2*M≤2^W)
    (old : ∀ i j,(m (field 8+i.val*2+j.val)).val=demand i j)
    (budget : ∀ i j e,MotifIntegerChoice.sentinel (demand i)+base j e<2^W) :
    RowResult (Execution.header cur 2 28 (choiceWords cur base size)) m (field 2)
      (fun i=>descriptor base size (demand i)) (closed (w:=W) (choiceWords cur base size)).binds := by
  apply run_rows cur m _ _ _ head field H (by decide) len cap
  intro i j a alt atArg outside
  have ha := header_frame cur m H outside (.inr atCur) (.inl hdr)
  have key (n : ℕ) (hn : n≤63) :
      nativeValue alt a (ptr cur n)=field n := by
    change (alt ((alt cur.val).val+n)).val=_
    rw [ha.pointer,ha.values n hn]
  apply choice_native cur alt a base size i.val j (demand i) (by rw [ha.pointer];have := ha.fit;omega)
    three table (by rw [key 2 (by decide)];exact atArg) (by rw [key 8 (by decide)];have := i.isLt;omega) _ (budget i)
  intro e
  simp only [nativeMemory]
  rw [key 8 (by decide),outside _ (.inr (by omega)),old]

include H in
theorem supplies_run (K : ℕ) (size bits : Fin (k+1)→ℕ) (pool : ∀ j,Fin (size j)→Fin 8→ℕ)
    (selected : Fin M→Fin (k+1)) (copies : Fin M→ℕ) (counts : ∀ i,Fin (size (selected i))→ℕ)
    (len : field 29=8*M) (cap : field 3+8*M<2^W) (atCur : field 3+8*M≤cur.val)
    (hdr : head+64≤field 3) (eight : 8<2^W) (table : k+1≤2^W) (alphabet : ∀ j,size j≤K)
    (prior : field 2+3*M≤field 3) (dense : field 1+K*M≤field 3)
    (tile : ∀ i,(m (field 2+i.val*3+1)).val=(selected i).val)
    (cr : ∀ i,(m (field 2+i.val*3)).val=copies i)
    (raw : ∀ i (s : Fin (size (selected i))),(m (field 1+i.val*K+s.val)).val=counts i s) :
    RowResult (Execution.header cur 3 29 (widthWords cur K size bits pool)) m (field 3)
      (fun i e=>copies i*bits (selected i)+∑ s,counts i s*pool (selected i) s e)
      (closed (w:=W) (widthWords cur K size bits pool)).binds := by
  apply run_rows cur m _ _ _ head field H (by decide) len cap
  intro i j a alt atArg outside
  have ha := header_frame cur m H outside (.inr atCur) (.inl hdr)
  have key (n : ℕ) (hn : n≤63) :
      nativeValue alt a (ptr cur n)=field n := by
    change (alt ((alt cur.val).val+n)).val=_
    rw [ha.pointer,ha.values n hn]
  have countBound : i.val*K+K≤K*M := by
    rw [←Nat.succ_mul,Nat.mul_comm K M]
    exact Nat.mul_le_mul_right K i.isLt
  apply supply_native cur alt a K size bits pool i.val (selected i) j (copies i) (counts i)
    (by rw [ha.pointer];have := ha.fit;omega) eight table (by rw [key 3 (by decide)];exact atArg)
    (by rw [key 2 (by decide)];have := i.isLt;omega) (by rw [key 1 (by decide)];omega) alphabet
  · simp only [nativeMemory]
    rw [key 2 (by decide),outside _ (.inl (by have := i.isLt;omega)),tile]
  · simp only [nativeMemory]
    rw [key 2 (by decide),outside _ (.inl (by have := i.isLt;omega)),cr]
  · intro s
    simp only [nativeMemory]
    rw [key 1 (by decide),outside _ (.inl (by have := (s.isLt.trans_le (alphabet _));omega)),raw]


open NavigationDirectory CompressorPacking.Native.ShrinkStage
variable {cur m}

theorem choices_cursor {K : ℕ} {c : Cursor} {x : Dimensions}
    (S : Resident.CursorSpace cur m c K x) (base : Fin (k+1)→Fin 2→ℕ) (size : Fin (k+1)→ℕ)
    (demand : Fin x.motifs→Fin 2→ℕ) (three : 3<2^W) (table : k+1≤2^W)
    (old : ∀ i j,(m ((Resident.pointers K c x).demands+i.val*2+j.val)).val=demand i j)
    (budget : ∀ i j e,MotifIntegerChoice.sentinel (demand i)+base j e<2^W) :
    RowResult (Execution.header cur 2 28 (choiceWords cur base size)) m c.heap
        (fun i=>descriptor base size (demand i)) (closed (w:=W) (choiceWords cur base size)).binds := by
  let p := Resident.pointers K c x
  have memsafe := S.separation
  have after : p.costs≤(allocate K c (.shrink x)).next.heap := by
    change p.costs≤extraEnd x (p.costs+2*(x.motifs+1))
    rw [extra_extent]
    omega
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8,e9⟩ := S.allocated
  have lim := after.trans S.controls
  change p.supply=p.choices+3*x.motifs at e1
  change p.choices=c.heap at e0
  change p.demands=p.supply+8*x.motifs at e2
  change p.split=p.demands+2*x.motifs at e3
  change p.colors=p.split+8*x.oldEdges at e4
  change p.offsets=p.colors+x.oldBase at e5
  change p.newGraph=p.offsets+x.oldBase at e6
  change p.keys=p.newGraph+6*x.newEdges at e7
  change p.newWidths=p.keys+x.newEdges at e8
  change p.costs=p.newWidths+x.newEdges*x.residual at e9
  have endFit := lim.trans_lt cur.isLt
  exact choices_run cur m S.header base size demand rfl (by change c.heap+3*x.motifs<_;omega)
    (by change c.heap+3*x.motifs≤_;omega) S.earlier three table
    (by change c.heap+3*x.motifs≤p.demands;omega) (by change p.demands+2*x.motifs≤_;omega) old budget

/-- Descriptor admission uses the physical canonical histogram family, with arbitrary dense raw words. -/
theorem choices_bank {K : ℕ} {c : Cursor} {x : Dimensions}
    (S : Resident.CursorSpace cur m c K x)
    (base : Fin (k+1)→Fin 2→ℕ) (size : Fin (k+1)→ℕ) (demand : Fin x.motifs→Fin 2→ℕ)
    (rows : HistogramRegister.Rows x.motifs K W) (raw : HistogramRegister.Words x.motifs K W)
    (result : RowResult (Execution.header cur 2 28 (choiceWords cur base size)) m c.heap
        (fun i=>descriptor base size (demand i)) (closed (w:=W) (choiceWords cur base size)).binds)
    (copies : ∀ i,descriptor base size (demand i) 0=rows.copies i)
    (symbols : ∀ i,descriptor base size (demand i) 2=rows.symbols i)
    (stored : ∀ i j,m (c.dense+K*i.val+j.val)=raw i j) :
    let after := ((Execution.header cur 2 28 (choiceWords cur base size)).run m).2
    AdmissionBank.Fits cur.val K after ∧ HistogramRegister.BankLayout cur.val rows raw after := by
  rw [result.image]
  let val := fun i=>descriptor base size (demand i)
  let after := denseFill c.heap val m
  have safe := S.allocated
  have stop : c.heap+3*x.motifs≤cur.val := by
    have top : (Resident.pointers K c x).costs≤(allocate K c (.shrink x)).next.heap := by
      change _≤extraEnd _ _;rw [extra_extent];omega
    obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8,e9⟩ := safe
    have := S.controls;omega
  have outside := dense_outside (m:=m) c.heap val
  have h := header_frame cur m S.header outside (.inr stop) (.inl S.earlier)
  have mc : AdmissionBank.rowCount cur.val after=x.motifs := by
    change (after (after cur.val).val).val=_
    rw [h.pointer]
    have count := h.values 0 (by decide)
    change (after (c.header+0)).val=x.motifs at count
    simpa only [Nat.add_zero] using count
  have md : AdmissionBank.denseBase cur.val after=c.dense := by
    change (after ((after cur.val).val+1)).val=_
    rw [h.pointer];exact h.values 1 (by decide)
  have mt : AdmissionBank.descBase cur.val after=c.heap := by
    change (after ((after cur.val).val+2)).val=_
    rw [h.pointer];exact h.values 2 (by decide)
  refine ⟨⟨cur.isLt,by rw [h.pointer];have := h.fit;omega,by rw [md,mc];have := S.counts;omega,
      by rw [mt,mc];omega⟩,mc,?_,?_,?_⟩
  · intro i
    rw [mt,Nat.mul_comm 3 i.val]
    have read := dense_at m c.heap val i (2:Fin 3)
    change after (c.heap+i.val*3+2)=(descriptor base size (demand i) 2:Word W) at read
    have hK : K*x.motifs≤c.heap := by have := S.counts;omega
    have hk := (Nat.le_mul_of_pos_right K (Nat.zero_lt_of_lt i.isLt)).trans hK
    have small : descriptor base size (demand i) 2<2^W := by
      rw [symbols i]
      exact (rows.fitSymbols i).trans_lt (hk.trans_lt (by have := cur.isLt; omega))
    exact (congrArg Fin.val read).trans ((Fin.val_cast_of_lt small).trans (symbols i))
  · intro i
    rw [mt,Nat.mul_comm 3 i.val]
    have read := dense_at m c.heap val i (0:Fin 3)
    change after (c.heap+i.val*3+0)=(descriptor base size (demand i) 0:Word W) at read
    rw [Nat.add_zero] at read
    have small : descriptor base size (demand i) 0<2^W := by
      rw [copies i]; exact rows.fitCopies i
    exact (congrArg Fin.val read).trans ((Fin.val_cast_of_lt small).trans (copies i))
  · intro i j
    rw [md,outside _ (.inl (by
      have lim := Nat.mul_le_mul_left K i.isLt
      rw [Nat.mul_succ] at lim
      have := j.isLt;have := S.counts;omega)),stored]



private theorem joined_scans {w : ℕ} (a b : Execution w) (input middle out : Memory w)
    (ta tb : ℕ)
    (left : a.fits input ∧ (a.run input).2=middle ∧ (a.run input).1=ta)
    (right : b.fits middle ∧ (b.run middle).2=out ∧ (b.run middle).1=tb) :
    (a.seq b).fits input ∧ ((a.seq b).run input).1=ta+tb ∧ ((a.seq b).run input).2=out := by
  change (a.fits input ∧ b.fits (a.run input).2) ∧
    (a.run input).1+(b.run (a.run input).2).1=ta+tb ∧ (b.run (a.run input).2).2=out
  rw [left.2.1,left.2.2,right.2.2]
  exact ⟨⟨left.1,right.1⟩,rfl,right.2.1⟩

/-- Native cost prefix and single mutable layout word, with every other header/arena word framed. -/
theorem scores_cursor {K : ℕ} {c : Cursor} {x : Dimensions} {A : Type} [Fintype A]
    (S : Resident.CursorSpace cur m c K x) (order : A ≃ Fin x.motifs) (width : A→Fin 8→ℕ)
    (B : ℕ) (bound : ∀ a e,width a e≤B) (scoreBound : 80*x.motifs*B^2<2^W) (two : 2<2^W)
    (reads : ∀ a e,(m ((Resident.pointers K c x).supply+(order a).val*8+e.val)).val=width a e) :
    let «prefix» := Execution.header cur 30 31 (prefixWords cur)
    let layout := Execution.header cur 32 33 (layoutWord cur)
    let E := «prefix».seq layout
    let lay := ShrinkMotif.chooseWidths width
    let out := (E.run m).2
    let p := Resident.pointers K c x
    E.fits m ∧ (E.run m).1 =
      (11+2*(x.motifs+1)*(2*(closed (w:=W) (prefixWords cur)).binds+4))+
      (11+(2*(closed (w:=W) (layoutWord cur)).binds+4)) ∧
      Resident.Header x p lay cur out ∧
      (∀ i,i ≠ c.header+27 → (i<p.costs ∨ p.costs+2*(x.motifs+1)≤ i) → out i=m i) ∧
      (∀ a e,(out (p.supply+(order a).val*8+e.val)).val=width a e) := by
  let p := Resident.pointers K c x
  let ext := fun i e=>if good : i<x.motifs then width (order.symm ⟨i,good⟩) e else 0
  let n := 2*(x.motifs+1)
  let cm := fillSegment p.costs n (scoreWord p.costs ext) m
  let e := allocate K c (.shrink x)
  let lay := ShrinkMotif.chooseWidths width
  let out := writeMemory cm ((c.header+27:ℕ):Word W) (if lay then 1 else 0)
  have extAt (a : A) : ext (order a).val=width a := by
    funext i;simp [ext,(order a).isLt]
  have endpt : p.costs+n≤e.next.heap := by
    change p.costs+n≤extraEnd x (p.costs+2*(x.motifs+1));rw [extra_extent];dsimp [n];omega
  obtain ⟨w0,w1,w2,w3,w4,w5,w6,w7,w8,w9⟩ := S.allocated
  have upper : p.costs+n≤cur.val := endpt.trans S.controls
  have supplyWhere : p.supply=c.heap+3*x.motifs := w1.trans (congrArg (·+3*x.motifs) w0)
  have srcEnd : p.supply+8*x.motifs≤p.costs := by
    change (Resident.pointers K c x).supply+8*x.motifs≤(Resident.pointers K c x).costs
    omega
  have hsep : c.header+64≤p.costs := by have := S.earlier;omega
  have bounded (i) (hi : i≤x.motifs) (b) : scorePrefix ext i b<2^W := by
    apply lt_of_le_of_lt (scorePrefix_bound ext i B b ?_) _
    · intro j hj f;simpa [ext,show j<x.motifs by omega] using bound (order.symm ⟨j,by omega⟩) f
    · exact (Nat.mul_le_mul_right (B^2) (Nat.mul_le_mul_left 80 hi)).trans_lt scoreBound
  have pr := prefix_run cur m c.header p.costs p.supply e.words S.header rfl rfl rfl
    (upper.trans_lt cur.isLt) two (.inl hsep) (.inr upper) (.inl srcEnd)
    (srcEnd.trans (by omega)) ext (fun i hi f=>by simpa [ext,hi] using reads (order.symm ⟨i,hi⟩) f) bounded
  have unchanged : agreesOutside p.costs (p.costs+n) cm m := fun i h=>segment_other m _ _ _ _ h
  have H := header_frame cur m S.header unchanged (.inr upper) (.inl hsep)
  have endHeader : c.header+27+1<2^W := by have := S.header.fit;omega
  have tail (f : Fin 2) : (cm (p.costs+2*x.motifs+f.val)).val=scorePrefix ext x.motifs (decide (f.val=1)) := by
    have addr : p.costs≤p.costs+2*x.motifs+f.val ∧ p.costs+2*x.motifs+f.val<p.costs+n := by
      have := f.isLt;dsimp [n];omega
    change (fillSegment p.costs n _ m _).val=_
    rw [fillSegment,ite_eq_left addr,scoreWord]
    have eq : p.costs+2*x.motifs+f.val-p.costs=x.motifs*2+f.val := by omega
    rw [eq,(parts x.motifs 2 f).1,(parts x.motifs 2 f).2,Fin.val_cast_of_lt (bounded _ le_rfl _)]
  have decideRun := layout_run cur cm c.header e.words H ext rfl rfl endHeader (by
      change p.costs+2*x.motifs+2≤_;dsimp [n] at upper;omega) tail
  have which : (if scorePrefix ext x.motifs true<scorePrefix ext x.motifs false then (1:Word W) else 0)=
      (if lay then 1 else 0) := by
    rw [scorePrefix_total order width ext extAt true,scorePrefix_total order width ext extAt false]
    by_cases better : ShrinkMotif.layoutCost width true < ShrinkMotif.layoutCost width false
    · simp [better,lay,ShrinkMotif.chooseWidths,Nat.not_le_of_lt better]
    · simp [better,lay,ShrinkMotif.chooseWidths,Nat.le_of_not_lt better]
  have lastMem := decideRun.2.1
  change ((Execution.header cur 32 33 (layoutWord cur)).run cm).2 =
    writeMemory cm ((c.header+27:ℕ):Word W)
      (if scorePrefix ext x.motifs true<scorePrefix ext x.motifs false then 1 else 0) at lastMem
  rw [which] at lastMem
  have ready := joined_scans (Execution.header cur 30 31 (prefixWords cur))
    (Execution.header cur 32 33 (layoutWord cur)) m cm out
    (11+n*(2*(closed (w:=W) (prefixWords cur)).binds+4))
    (11+(2*(closed (w:=W) (layoutWord cur)).binds+4)) pr ⟨decideRun.1,lastMem,decideRun.2.2⟩
  have image := ready.2.2
  have apart (i : ℕ) (h : i≠c.header+27) (v : i<p.costs ∨ p.costs+n≤ i) : out i=m i := by
    change (if i=((c.header+27:ℕ):Word W).val then _ else cm i)=_
    rw [Fin.val_cast_of_lt (by omega),ite_eq_right h,unchanged _ v]
  refine ⟨ready.1,ready.2.1,?_,?_,?_⟩
  · rw [image]
    refine ⟨by rw [apart _ (by omega) (.inr upper)];exact S.header.pointer,by have := S.header.fit;change c.header+34≤_;omega,?_⟩
    intro i
    change out (c.header+i.val)=(Resident.value x p lay i.val:Word W)
    by_cases h : i.val=27
    · change (if c.header+i.val=((c.header+27:ℕ):Word W).val then _ else cm _)=_
      rw [Fin.val_cast_of_lt (by omega),h,ite_eq_left rfl]
      cases lay <;> rfl
    · rw [apart (c.header+i.val) (by omega) (.inl (by have := i.isLt;omega))]
      have prev : m (c.header+i.val)=(Resident.value x p false i.val:Word W) := S.pristine.words i
      simpa only [Resident.value,selected,ite_eq_right h] using prev
  · rw [image];exact apart
  · intro a f
    rw [image,apart _ (by have := S.earlier;omega) (.inl (by have := (order a).isLt;have := f.isLt;omega)),reads]


open RefreshDemandRows.Static RAM.MotifRows

/-- The four expressions' coefficients are independent of machine word size and the current pointer. -/
theorem scan_work {k : ℕ} (base : Fin (k+1)→Fin 2→ℕ) (size bits : Fin (k+1)→ℕ)
    (pool : ∀ j,Fin (size j)→Fin 8→ℕ) (K : ℕ) (cur : Word W) {U : ℕ} (ref : Word U) :
    Same (choiceWords cur base size) (choiceWords ref base size) ∧
    Same (widthWords cur K size bits pool) (widthWords ref K size bits pool) ∧
    Same (prefixWords cur) (prefixWords ref) ∧ Same (layoutWord cur) (layoutWord ref) := by
  let fs := fun {w} (c : Word w) (e : Fin 2)=>RAM.MotifRows.field
    (atRow (ptr c 8) (.op .div (rel c 2) (.lit 3)) 2) e.val
  let z := fun {w} (c : Word w)=>RefreshDemandRows.chooseFields (fs c) base
  have a : PairSame (z cur) (z ref) := choice_work _ _ base (fun _=>rfl)
  have l : Same (RefreshDemandRows.rowAt _ (fun j=>.lit (size j)) (z cur).2)
      (RefreshDemandRows.rowAt _ (fun j=>.lit (size j)) (z ref).2) :=
    lookup_work _ _ a.2 (fun _=>rfl)
  refine ⟨?_,?_,rfl,rfl⟩
  · change _+_+(z cur).1.work+(_+_+(z cur).2.work+_+1)+1 =
      _+_+(z ref).1.work+(_+_+(z ref).2.work+_+1)+1
    rw [a.1,a.2,l]
    rfl
  · unfold widthWords
    apply lookup_work
    · rfl
    · intro j
      apply lookup_work
      · rfl
      · intro e
        apply pool_work
        · rfl
        · rfl

theorem calls_linear {k : ℕ} (base : Fin (k+1)→Fin 2→ℕ) (size bits : Fin (k+1)→ℕ)
    (pool : ∀ j,Fin (size j)→Fin 8→ℕ) (K : ℕ) :
    ∃ B : ℕ,∀ W (cur : Word W) M,
      (11+3*M*(2*(closed (w:=W) (choiceWords cur base size)).binds+4))+
        (11+8*M*(2*(closed (w:=W) (widthWords cur K size bits pool)).binds+4))+
        (11+2*(M+1)*(2*(closed (w:=W) (prefixWords cur)).binds+4))+
        (11+(2*(closed (w:=W) (layoutWord cur)).binds+4))≤44+B*(M+1) := by
  let z : Word 1 := 0
  let a := 2*(choiceWords z base size).work+4
  let b := 2*(widthWords z K size bits pool).work+4
  let c := 2*(prefixWords z).work+4
  let d := 2*(layoutWord z).work+4
  refine ⟨3*a+8*b+2*c+d,?_⟩
  intro W cur M
  have h := scan_work base size bits pool K cur z
  simp only [binds_closed,h.1,h.2.1,h.2.2.1,h.2.2.2]
  change 11+3*M*a+(11+8*M*b)+(11+2*(M+1)*c)+(11+d)≤44+(3*a+8*b+2*c+d)*(M+1)
  nlinarith only [Nat.zero_le (3*a),Nat.zero_le (8*b),Nat.zero_le (d*M)]

/-- A live row is interpreted through its actual tile and alphabet. -/
theorem issued_row {F : Type} [Field F] {J : Type*} (T : ShrinkMotif.Table F)
    (b : Fin 2→ℕ) (r : ℕ) (v : J) (index : J→T.Row)
    (hrow : index v=MotifIntegerChoice.best (MotifIntegerChoice.score b T.base) T.first T.more)
    (x : MotifOuterTerms.Histogram (T.block (index v)).Alphabet r)
    (raw : ℕ→ℕ) (read : ∀ a,raw ((Fintype.equivFin _ a).val)=(x.val a).val) (e : Fin 8) :
    let j := RefreshDemandRows.tileNumber b (T.base ∘ T.row)
    r*(T.block (T.row j)).bits+∑ i:Fin (Fintype.card (T.block (T.row j)).Alphabet),
      raw i.val*(T.block (T.row j)).output ((Fintype.equivFin _).symm i) e =
      MotifOuterTerms.histWidth (T.block (index v)).output x e+r*(T.block (index v)).bits := by
  dsimp only
  rw [(T.row_chosen b).trans hrow.symm,Nat.add_comm]
  congr 1
  rw [←(Fintype.equivFin (T.block (index v)).Alphabet).sum_comp]
  simp only [read,Equiv.symm_apply_apply,MotifOuterTerms.histWidth]


end
end ThreeFlat.Diagonal.ShrinkStageNav

namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking Native PhysicalShrink MotifOuterTerms
open RefreshDemandRows MotifIntegerChoice ShrinkStageNav NavigationPass NavigationDirectory
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024) (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "P" => shrinkRecordPacking s rem A
local notation "ord" => shrinkRecordOrder s rem A
local notation "cc" => (show 2≤2*(2^s)+1 from by have := Nat.two_pow_pos s;omega)
local notation "demand" => PhysicalShrink.b P (shrinkRecordWidth s rem A) (shrinkRecordCode s rem A) cc
local notation "sizes" => fun j=>Fintype.card (T.block (T.row j)).Alphabet
local notation "X" => ShrinkStage.Resident.dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base) (tagBits (2^s)) rem

set_option maxHeartbeats 800000 in
theorem native_shrink_choice {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
    (S : ShrinkStage.Resident.CursorSpace cur m c K X) (fit : (Q).Fits K W)
    (x : HistogramRegister.Words (Q).motifs K W)
    (raw : ∀ i j,m (c.dense+K*i.val+j.val)=x i j)
    (words : ∀ a j,(m ((ShrinkStage.Resident.pointers K c X).demands+(ord a).val*2+j.val)).val=demand a j)
    (three : 3<2^W) (count : T.more.length+1≤2^W)
    (bound : ∀ a j e,sentinel (demand a)+T.base (T.row j) e<2^W) :
    let E := shrinkChoices cur T
    let out := (E.run m).2
    E.fits m ∧ (E.run m).1=11+3*(Q).motifs*(2*(RAM.HeaderScan.closed (w:=W) (choiceWords cur (T.base ∘ T.row) sizes)).binds+4) ∧
      AdmissionBank.Fits cur.val K out ∧ HistogramRegister.BankLayout cur.val ((Q).rows fit) x out ∧
      (∀ i : Fin (Q).motifs,(out (c.heap+i.val*3+1)).val=(tileNumber (demand ((ord).symm i)) (T.base ∘ T.row)).val) ∧
      RAM.DescriptorScan.agreesOutside c.heap (c.heap+3*(Q).motifs) out m := by
  let order : (P).Motif ≃ Fin (X).motifs := ord
  let dd (i : Fin (X).motifs) := demand (order.symm i)
  let desc (i : Fin (X).motifs) := descriptor (T.base ∘ T.row) sizes (dd i)
  have measured (i : Fin (X).motifs) (j : Fin 2) :
      (m ((ShrinkStage.Resident.pointers K c X).demands+i.val*2+j.val)).val=dd i j :=
    (congrArg (fun k : Fin (X).motifs =>
      (m ((ShrinkStage.Resident.pointers K c X).demands+k.val*2+j.val)).val)
      (order.apply_symm_apply i).symm).trans (words (order.symm i) j)
  have row := choices_cursor S (T.base ∘ T.row) sizes dd three count measured (fun i=>bound (order.symm i))
  have choose (i : Fin (X).motifs) : T.row (tileNumber (dd i) (T.base ∘ T.row)) =
      picked T P (shrinkRecordWidth s rem A) (shrinkRecordCode s rem A) cc ((ord).symm i) := T.row_chosen _
  have cb := choices_bank S (T.base ∘ T.row) sizes dd ((Q).rows fit) x row
    (fun i=>congrArg (score (dd i) T.base) (choose i))
    (fun i=>congrArg (fun j=>Fintype.card (T.block j).Alphabet) (choose i)) raw
  refine ⟨row.fits,row.clocks,cb.1,cb.2,?_,?_⟩
  · intro i
    have read := congrArg (fun img : Memory W=>img (c.heap+i.val*3+1)) row.image
    have word := read.trans (dense_at m c.heap desc i (1:Fin 3))
    exact (congrArg Fin.val word).trans
      (Fin.val_cast_of_lt ((tileNumber (dd i) (T.base ∘ T.row)).isLt.trans_le count))
  · change RAM.DescriptorScan.agreesOutside _ _ ((Execution.header cur 2 28 _).run m).2 m
    rw [row.image]
    exact dense_outside (m:=m) _ _


open private branchFintype from OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily

local instance : Fintype (shrinkRecordHists T s rem A) :=
  branchFintype T (shrinkRecordState s rem A) (shrinkRecordLane s rem) (shrinkRecordPacking s rem A)
    (Nat.two_pow_pos s) (shrinkRecordCode s rem A)

abbrev shrinkIssuedBranch (branch : Fin (shrinkBinary T s D rem hD small A).rules.count) :=
  (Fintype.equivFin (shrinkRecordHists T s rem A)).symm (branch.cast (shrinkBinary_ruleCount T s D rem hD small A))

abbrev shrinkIssuedWords (branch : Fin (shrinkBinary T s D rem hD small A).rules.count) :=
  issued T P (shrinkRecordWidth s rem A) (shrinkRecordCode s rem A) cc
    (shrinkIssuedBranch T s D rem hD small A branch)

abbrev shrinkIssuedScan {W : ℕ} (cur : Word W) (K : ℕ) :=
  Execution.header cur 3 29 (widthWords cur K sizes (fun i=>(T.block (T.row i)).bits)
    (fun i a e=>(T.block (T.row i)).output ((Fintype.equivFin _).symm a) e))

theorem native_shrink_supply {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
    (S : ShrinkStage.Resident.CursorSpace cur m c K X) (fit : (Q).Fits K W) (branch : Fin (shrinkBinary T s D rem hD small A).rules.count)
    (bank : HistogramRegister.BankLayout cur.val ((Q).rows fit) (HistogramRegister.words ((Q).rows fit) ((Q).sequence fit branch)) m)
    (tile : ∀ i : Fin (Q).motifs,(m (c.heap+i.val*3+1)).val=(tileNumber (demand ((ord).symm i)) (T.base ∘ T.row)).val)
    (eight : 8<2^W) (count : T.more.length+1≤2^W) (alphabet : ∀ j,sizes j≤K) :
    let E := shrinkIssuedScan T cur K
    let h := shrinkIssuedWords T s D rem hD small A branch
    E.fits m ∧ (E.run m).2=denseFill (ShrinkStage.Resident.pointers K c X).supply (fun i=>h ((ord).symm i)) m ∧
    (E.run m).1=11+8*(Q).motifs*(2*(RAM.HeaderScan.closed (w:=W) (widthWords cur K sizes (fun j=>(T.block (T.row j)).bits)
      (fun j a e=>(T.block (T.row j)).output ((Fintype.equivFin _).symm a) e))).binds+4) := by
  let u := fun i : Fin (Q).motifs=>tileNumber (demand ((ord).symm i)) (T.base ∘ T.row)
  let counts := fun (i : Fin (Q).motifs) (a : Fin (sizes (u i)))=>(m (c.dense+i.val*K+a.val)).val
  let cs := fun i : Fin (Q).motifs=>(Q).copies i
  let bit := fun j=>(T.block (T.row j)).bits
  let pool := fun j (a : Fin (sizes j)) e=>(T.block (T.row j)).output ((Fintype.equivFin _).symm a) e
  let p := ShrinkStage.Resident.pointers K c X
  have dense : AdmissionBank.denseBase cur.val m=c.dense := by
    change (m ((m cur.val).val+1)).val=_
    rw [S.header.pointer];exact S.header.values 1 (by decide)
  have ch : AdmissionBank.descBase cur.val m=c.heap := by
    change (m ((m cur.val).val+2)).val=_
    rw [S.header.pointer];exact S.header.values 2 (by decide)
  have copies (i : Fin (Q).motifs) : (m (c.heap+i.val*3)).val=cs i := by
    simpa only [ch,Nat.mul_comm 3 i.val,cs,RecordFamily.rows] using bank.copies i
  have top : p.costs≤(allocate K c (.shrink X)).next.heap := by
    change p.costs≤ShrinkStage.extraEnd X (p.costs+2*((X).motifs+1))
    rw [ShrinkStage.extra_extent]
    omega
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8,e9⟩ := S.allocated
  have limit := top.trans S.controls
  have supplyBase : c.heap+3*(X).motifs = p.supply := by
    change p.choices=c.heap at e0
    change p.supply=p.choices+3*(X).motifs at e1
    rw [e1,e0]
  have supplyEnd : p.supply+8*(X).motifs ≤ cur.val := by
    dsimp only [p] at limit ⊢
    omega
  have res := supplies_run cur m S.header K sizes bit pool u cs counts rfl
    (supplyEnd.trans_lt cur.isLt) supplyEnd
    (S.earlier.trans ((Nat.le_add_right c.heap _).trans_eq supplyBase)) eight count alphabet
    supplyBase.le (S.counts.trans ((Nat.le_add_right c.heap _).trans_eq supplyBase))
    tile copies (fun _ _=>rfl)
  refine ⟨res.fits,res.image.trans ?_,res.clocks⟩
  apply congrArg (fun z : Fin (Q).motifs → Fin 8 → ℕ => denseFill p.supply z m)
  funext i e
  let a := (ord).symm i
  let t := shrinkIssuedBranch T s D rem hD small A branch
  have countRead (v : (Q).alphabet i) :
      (m (c.dense+i.val*K+(Fintype.equivFin _ v).val)).val =
        ((t a).val v).val := by
    let j := (Fintype.equivFin _ v).castLE (fit.1 i)
    have row := congrArg Fin.val (bank.words i j)
    rw [dense,Nat.mul_comm K i.val] at row
    exact row.trans ((Q).words_val fit branch i v)
  let pick := picked T P (shrinkRecordWidth s rem A) (shrinkRecordCode s rem A) cc
  exact issued_row T (demand a) (cs i) a pick rfl (t a) (fun j=>(m (c.dense+i.val*K+j)).val) countRead e



/-- This is exactly the first component in the installed `NavigationPass.shrinkPublish`. -/
abbrev shrinkCostScans {W : ℕ} (cur : Word W) (K : ℕ) :=
  (shrinkIssuedScan T cur K).seq ((Execution.header cur 30 31 (prefixWords cur)).seq
    (Execution.header cur 32 33 (layoutWord cur)))

theorem native_shrink_commit {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor)
    (S : ShrinkStage.Resident.CursorSpace cur m c K X) (fit : (Q).Fits K W)
    (branch : Fin (shrinkBinary T s D rem hD small A).rules.count)
    (bank : HistogramRegister.BankLayout cur.val ((Q).rows fit) (HistogramRegister.words ((Q).rows fit) ((Q).sequence fit branch)) m)
    (tile : ∀ i : Fin (Q).motifs,(m (c.heap+i.val*3+1)).val=(tileNumber (demand ((ord).symm i)) (T.base ∘ T.row)).val)
    (eight : 8<2^W) (count : T.more.length+1≤2^W) (alphabet : ∀ j,sizes j≤K)
    (B : ℕ) (widthBound : ∀ a e,shrinkIssuedWords T s D rem hD small A branch a e≤B)
    (widthFits : B<2^W) (scoreFits : 80*(Q).motifs*B^2<2^W) :
    let E := shrinkCostScans T cur K
    let z := (E.run m).2
    let p := ShrinkStage.Resident.pointers K c X
    let widths := shrinkIssuedWords T s D rem hD small A branch
    E.fits m ∧ (E.run m).1=
        ((shrinkIssuedScan T cur K).run m).1 +
        ((11+2*((Q).motifs+1)*(2*(RAM.HeaderScan.closed (w:=W) (prefixWords cur)).binds+4))+
        (11+(2*(RAM.HeaderScan.closed (w:=W) (layoutWord cur)).binds+4))) ∧
      ShrinkStage.Resident.Header X p (ShrinkMotif.chooseWidths widths) cur z ∧
      (∀ a e,z (p.supply+(ord a).val*8+e.val)=(widths a e:Word W)) ∧
      (∀ i,i≠c.header+27 → (i<p.costs ∨ p.costs+2*((Q).motifs+1)≤ i) →
        (i<p.supply ∨ p.supply+8*(Q).motifs≤ i) → z i=m i) := by
  let E := shrinkIssuedScan T cur K
  let p := ShrinkStage.Resident.pointers K c X
  let widths := shrinkIssuedWords T s D rem hD small A branch
  let v := fun (i : Fin (Q).motifs)=>widths ((ord).symm i)
  let mid := (E.run m).2
  have motifs : (Q).motifs=(X).motifs := rfl
  have ii := native_shrink_supply T s D rem hD small A cur m c S fit branch bank tile eight count alphabet
  have iss : mid=denseFill p.supply v m := ii.2.1
  have frame : RAM.DescriptorScan.agreesOutside p.supply (p.supply+8*(Q).motifs) mid m := by
    rw [iss];exact dense_outside (m:=m) _ _
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8,e9⟩ := S.allocated
  have hi : p.costs≤(allocate K c (.shrink X)).next.heap := by
    change p.costs≤ShrinkStage.extraEnd X (p.costs+2*((X).motifs+1))
    rw [ShrinkStage.extra_extent]
    omega
  have stop := hi.trans S.controls
  have endSupply : p.supply+8*(Q).motifs≤cur.val := by
    rw [motifs]
    dsimp only [p] at stop ⊢
    omega
  have beginSupply : c.header+64≤p.supply := by
    have := S.earlier
    dsimp only [p]
    omega
  have mh : ShrinkStage.Resident.CursorSpace cur mid c K X :=
    {S with header := header_frame cur m S.header frame (.inr endSupply) (.inl beginSupply)}
  have writes (a) (e) : (mid (p.supply+(ord a).val*8+e.val)).val=widths a e := by
    rw [iss,dense_at m p.supply v (ord a) e,Fin.val_cast_of_lt]
    · simp [v]
    · simpa [v] using (widthBound a e).trans_lt widthFits
  have scan := scores_cursor mh ord widths B widthBound scoreFits (by omega) writes
  refine ⟨⟨ii.1,scan.1⟩,?_,scan.2.2.1,?_,?_⟩
  · change (E.run m).1+_=_
    rw [scan.2.1]
    rfl
  · intro a e
    exact (Fin.cast_val_eq_self _).symm.trans
      (congrArg (fun n : ℕ => (n : Word W)) (scan.2.2.2.2 a e))
  · intro i block left right
    exact (scan.2.2.2.1 i block left).trans (frame _ right)



def shrinkBaseBound := Finset.univ.sup (fun j:T.Row=>Finset.univ.sup (T.base j))

theorem prior_width_le (e) : shrinkRecordWidth s rem A e≤A.maxWidth := by
  have cast_max {d i j : ℕ} (eqv : i=j) (a : State d i) : (eqv ▸ a : State d j).maxWidth=a.maxWidth := by
    cases eqv;rfl
  exact ((shrinkRecordState s rem A).width_le_maxWidth _).trans_eq (cast_max _ _)

theorem shrink_choice_room {W : ℕ}
    (room : 1+2*(widthMultiplicity (2*(2^s)+1) (2^s)*A.maxWidth)+shrinkBaseBound T<2^W) :
    ∀ a j e,sentinel (demand a)+T.base (T.row j) e<2^W := by
  intro a j e
  have wd (i : Fin 2) := demandWidth_le P (shrinkRecordWidth s rem A) (motifNumbers P (shrinkRecordCode s rem A) cc)
    (prior_width_le s rem A) a i
  have tab : T.base (T.row j) e≤ shrinkBaseBound T := (Finset.le_sup (s:=Finset.univ) (f:=T.base (T.row j))
    (Finset.mem_univ e)).trans (Finset.le_sup (s:=Finset.univ) (f:=fun z=>Finset.univ.sup (T.base z)) (Finset.mem_univ (T.row j)))
  rw [sentinel,Fin.sum_univ_two]
  have l0 := wd 0;have l1 := wd 1
  change demand a 0≤_ at l0; change demand a 1≤_ at l1
  omega

theorem shrink_issued_room (branch : Fin (shrinkBinary T s D rem hD small A).rules.count) :
    ∀ a e,shrinkIssuedWords T s D rem hD small A branch a e≤
      shrinkMotifWidthFactor T (2*(2^s)+1) (2^s)*(1+A.maxWidth) :=
  PhysicalShrink.issued_le P (shrinkRecordWidth s rem A) T (shrinkRecordCode s rem A) cc
    (prior_width_le s rem A) (shrinkIssuedBranch T s D rem hD small A branch)



end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
