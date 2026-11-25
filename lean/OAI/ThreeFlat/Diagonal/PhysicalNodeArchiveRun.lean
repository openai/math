import OAI.ThreeFlat.Diagonal.NavigationPackedMount
import OAI.ThreeFlat.Diagonal.PhysicalNodeTape
import OAI.ThreeFlat.Diagonal.PhysicalNodePublication

namespace OAI
/-! # Execution of the packed chronological node archive -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open scoped Fin.CommRing Classical BigOperators

variable {W : ℕ} {rows : List Layers}

structure Program (rows : List Layers) where
  data : (i : Fin rows.length) → LayerData (rows.get i).actual
  owners : (i : Fin rows.length) → Fin (rows.get i).actual.count → ℕ

def image (a : NodeArchive) (n : ℕ) : PackedStageArchive.Layout :=
  ⟨a.phase,a.rawHeader,a.rawHeader,a.headerBase,16*n⟩

def hdr (a : NodeArchive) (k : ℕ) := a.headerBase+16*k

def initial (a : NodeArchive) (rows : List Layers) (m : Memory W) : Memory W :=
  writeMemory (writeMemory (fillSegment a.headerBase (16*rows.length) (tapeWord a rows) m)
    (a.banks.current:Word W) (a.headerBase:Word W)) (a.counter:Word W) (rows.length:Word W)

def decrement (a : NodeArchive) (m : Memory W) :=
  writeMemory m (a.counter:Word W) (m (a.counter:Word W).val-1)

def prior (a : NodeArchive) (m : Memory W) (id : ℕ) (c : Fin 2) :=
  (m (a.banks.charges+2*id+c.val)).val

def nextState (a : NodeArchive) (P : Program rows) (i : Fin rows.length) (m : Memory W) : Memory W :=
  let row := rows.get i
  let dec := decrement a m
  emitted a.banks row.actual row.parent (hdr a (i.val+1)) dec
    ((P.data i).cost a.banks (prior a dec)) (P.owners i)

/-- Exact RAM after the packed image, both start instructions and the first k visits. -/
def state (a : NodeArchive) (P : Program rows) (m : Memory W) : ℕ → Memory W
  | 0 => initial a rows m
  | k+1 => if h : k<rows.length then nextState a P ⟨k,h⟩ (state a P m k) else state a P m k

theorem state_step (a : NodeArchive) (P : Program rows) (m : Memory W) (i : Fin rows.length) :
    state a P m (i.val+1)=nextState a P i (state a P m i.val) := by
  rw [state,dite_eq_left i.isLt]

def outside (base count x : ℕ) := x<base ∨ base+count≤x

def keeps (a : NodeArchive) (row : Layers) (x : ℕ) : Prop :=
  x≠a.counter ∧ x≠a.banks.current ∧
  outside (a.banks.charges+2*row.actual.first) (2*row.actual.count) x ∧
  outside (a.banks.nodes+8*row.actual.first) (8*row.actual.count) x

private theorem segment_keeps (m : Memory W) (base count x : ℕ) (word : ℕ→Word W)
    (off : outside base count x) : fillSegment base count word m x=m x := by
  have skip : ¬(base≤x ∧ x<base+count) := by rcases off with h|h <;> omega
  simp only [fillSegment,ite_eq_right skip]

private theorem emit_keeps (a : NodeArchive) (row : Layers) (next : ℕ) (m : Memory W)
    (val : Fin row.actual.count→Fin 2→ℕ) (own : Fin row.actual.count→ℕ) (x : ℕ)
    (ctl : a.banks.current<2^W) (different : x≠a.banks.current)
    (c : outside (a.banks.charges+2*row.actual.first) (2*row.actual.count) x)
    (n : outside (a.banks.nodes+8*row.actual.first) (8*row.actual.count) x) :
    emitted a.banks row.actual row.parent next m val own x=m x := by
  simp only [emitted,writeMemory,Fin.val_cast_of_lt ctl,ite_eq_right different,recorded,charged]
  rw [segment_keeps _ _ _ _ _ n,segment_keeps _ _ _ _ _ c]

theorem nextState_keeps (a : NodeArchive) (P : Program rows) (i : Fin rows.length) (m : Memory W)
    (x : ℕ) (ctr : a.counter<2^W) (ctl : a.banks.current<2^W) (off : keeps a (rows.get i) x) :
    nextState a P i m x=m x := by
  obtain ⟨hc,hs,charge,node⟩:=off
  unfold nextState
  rw [emit_keeps a (rows.get i) _ _ _ _ x ctl hs charge node]
  simp only [decrement,writeMemory,Fin.val_cast_of_lt ctr,ite_eq_right hc]

/-- In particular, packed source bits and every earlier bank row retain their physical words
through any suffix whose two write ranges avoid their addresses. -/
theorem state_keeps (a : NodeArchive) (P : Program rows) (m : Memory W) (x lo hi : ℕ)
    (ordered : lo≤hi) (last : hi≤rows.length) (ctr : a.counter<2^W) (ctl : a.banks.current<2^W)
    (off : ∀ i : Fin rows.length, lo≤ i.val → i.val<hi → keeps a (rows.get i) x) :
    state a P m hi x=state a P m lo x := by
  induction hi,ordered using Nat.le_induction with
  | base => rfl
  | succ k lower ih =>
    let i : Fin rows.length := ⟨k,by omega⟩
    rw [show k+1=i.val+1 by rfl,state_step]
    exact (nextState_keeps a P i _ x ctr ctl (off i lower (Nat.lt_succ_self _))).trans
      (ih (by omega) (fun j l h=>off j l (by omega)))

structure RunBounds (W : ℕ) (a : NodeArchive) (rows : List Layers) (budget : ℕ) : Prop where
  counter : a.counter<a.banks.charges
  controls : a.counter≠a.banks.current
  counterSize : a.counter<2^W
  pointerSize : a.banks.current<2^W
  countSize : rows.length<2^W
  layer : ∀ i : Fin rows.length, Bounds W a.banks (rows.get i).actual (rows.get i).parent
    (hdr a i.val) a.childCap a.halfCap a.motifCap
  time : ∀ i : Fin rows.length, ticks W a.banks a.childCap a.halfCap a.motifCap (rows.get i).actual.count≤budget

def bodyReady (a : NodeArchive) (P : Program rows) (m : Memory W) (i : Fin rows.length) : Prop :=
  let dec := decrement a (state a P m i.val)
  StageInput a.banks (P.data i) (rows.get i).parent (hdr a i.val) (hdr a (i.val+1)) a.halfCap a.motifCap
    (P.owners i) (prior a dec) dec

private theorem next_count (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (i : Fin rows.length) {z : ℕ} (count : (m (a.counter:Word W).val).val=z+1) :
    ((nextState a P i m) (a.counter:Word W).val).val=z := by
  have below := room.counter
  have node := (room.layer i).chargeEnd
  rw [Fin.val_cast_of_lt room.counterSize] at count
  have word : m a.counter ≠ 0 := by
    intro h
    rw [h] at count
    change 0=z+1 at count
    omega
  unfold nextState
  rw [Fin.val_cast_of_lt room.counterSize]
  rw [emit_keeps a (rows.get i) _ _ _ _ _ room.pointerSize room.controls (.inl (by omega)) (.inl (by omega))]
  simp only [decrement,writeMemory,Fin.val_cast_of_lt room.counterSize,ite_true]
  rw [Fin.val_sub_one_of_ne_zero word,count,Nat.add_sub_cancel]

theorem counted_run (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (ready : ∀ i, bodyReady a P m i) :
    (loop (a.counter:Word W) (NavigationNodeRows.procedure a.banks a.childCap a.halfCap a.motifCap)).Spec
      (fun x=>x=initial a rows m) (fun _ out=>out=state a P m rows.length)
      (rows.length*(7+budget)+4) := by
  let inv (z : ℕ) (x : Memory W) := z≤rows.length ∧ x=state a P m (rows.length-z)
  have step (z : ℕ) (x : Memory W) (ok : inv (z+1) x) (count : (x (a.counter:Word W).val).val=z+1) :
      (NavigationNodeRows.procedure a.banks a.childCap a.halfCap a.motifCap).Spec
        (fun y=>y=decrement a x) (fun _ out=>(out (a.counter:Word W).val).val=z ∧ inv z out) budget := by
    have within := ok.1
    let i : Fin rows.length := ⟨rows.length-(z+1),by omega⟩
    have eq : x=state a P m i.val := ok.2
    let dec := decrement a x
    have input : StageInput a.banks (P.data i) (rows.get i).parent (hdr a i.val) (hdr a (i.val+1))
        a.halfCap a.motifCap (P.owners i) (prior a dec) dec := by simpa only [bodyReady,dec,eq] using ready i
    have iter : (NavigationNodeRows.procedure a.banks a.childCap a.halfCap a.motifCap).Spec
        (fun y=>y=decrement a x) (fun _ out=>(out (a.counter:Word W).val).val=z ∧ inv z out) budget := by
      intro labels regs slots
      apply Procedure.Spec.mono (publish_layer_spec (room.layer i) input) (fun _ h=>h) _ (room.time i)
      intro _ o h
      change o=nextState a P i x at h
      subst o
      refine ⟨next_count a P x room i count,by omega,?_⟩
      have atNext : rows.length-z=i.val+1 := by dsimp [i];omega
      rw [atNext,state_step,eq]
    intro labels regs slots machine
    exact iter machine
  intro labels regs slots
  apply Procedure.Spec.mono (Procedure.counted_spec _ (a.counter:Word W) rows.length budget inv step) ?_ ?_ le_rfl
  · rintro x rfl
    refine ⟨⟨le_rfl,by simp [state]⟩,?_⟩
    simp only [initial,writeMemory,ite_true,Fin.val_cast_of_lt room.countSize]
  · intro _ out h;simpa only [Nat.sub_zero] using h.2

/-- This is the actual packed-header decoder, both three-instruction initializers and the
single counted native layer publisher. The postcondition names its complete RAM image. -/
theorem publish_spec (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (loaded : Mount (image a rows.length) (tapeWord a rows) m) (room : RunBounds W a rows budget)
    (ready : ∀ i, bodyReady a P m i) :
    (a.publish rows.length).Spec (fun x=>x=m) (fun _ out=>out=state a P m rows.length)
      ((16*rows.length*(5*W+6)+10)+(3+(3+(rows.length*(7+budget)+4)))) := by
  let mounted:=fillSegment a.headerBase (16*rows.length) (tapeWord a rows) m
  let pointing:=writeMemory mounted (a.banks.current:Word W) (a.headerBase:Word W)
  have pointer : (start (a.banks.current:Word W) (a.headerBase:Word W)).Spec
      (·=mounted) (fun _ out=>out=pointing) 3 :=
    Procedure.Spec.atMemory (start_spec _ _) mounted trivial
  have counter : (start (a.counter:Word W) (rows.length:Word W)).Spec
      (·=pointing) (fun _ out=>out=initial a rows m) 3 :=
    Procedure.Spec.atMemory (start_spec _ _) pointing trivial
  intro labels regs slots
  apply Procedure.Spec.mono
    (Procedure.Spec.seq (mount_spec (image a rows.length) (tapeWord a rows) m loaded)
      (Procedure.Spec.seq pointer
        (Procedure.Spec.seq counter (counted_run a P m room ready) (fun _ _ out=>out))
        (fun _ _ out=>out))
      (fun _ _ out=>out)) (fun _ h=>h) ?_ le_rfl
  rintro _ _ ⟨_,_,_,_,_,_,out⟩
  exact out

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open scoped Fin.CommRing Classical BigOperators
variable {W : ℕ} {rows : List Layers}

private theorem tape_get (b : Banks) (base : ℕ) (xs : List Layers) (i : Fin xs.length) (j : Fin 16) :
    (nodeTape b base xs)[16*i.val+j.val]? =
      some (header b (xs.get i).actual (xs.get i).parent (base+16*(i.val+1)) j.val) := by
  induction xs generalizing base with
  | nil => exact Fin.elim0 i
  | cons row tail ih =>
    let first := List.ofFn (fun t : Fin 16 => header b row.actual row.parent (base+16) t.val)
    have len : first.length = 16 := List.length_ofFn
    obtain ⟨_ | k,hk⟩ := i
    · simp only [Nat.mul_zero,Nat.zero_add,Nat.mul_one]
      change (first++nodeTape b (base+16) tail)[j.val]? = some (header b row.actual row.parent (base+16) j.val)
      rw [List.getElem?_append_left (show j.val<first.length by rw [len];exact j.isLt)]
      simp only [first,List.getElem?_ofFn,dite_eq_left j.isLt]
    · let t : Fin tail.length := ⟨k,by simpa using hk⟩
      change (first++nodeTape b (base+16) tail)[16*(k+1)+j.val]? =
        some (header b (tail.get t).actual (tail.get t).parent (base+16*((k+1)+1)) j.val)
      rw [List.getElem?_append_right (show first.length≤16*(k+1)+j.val by omega),
        show 16*(k+1)+j.val-first.length=16*k+j.val by omega,
        ←show base+16+16*(k+1)=base+16*((k+1)+1) by omega]
      exact ih (base+16) t

theorem tapeWord_read (a : NodeArchive) (i : Fin rows.length) (j : Fin 16) :
    tapeWord (W:=W) a rows (hdr a i.val+j.val)=
      (header a.banks (rows.get i).actual (rows.get i).parent (hdr a (i.val+1)) j.val:Word W) := by
  have sub : hdr a i.val+j.val-a.headerBase=16*i.val+j.val := by dsimp [hdr];omega
  unfold tapeWord
  rw [sub,tape_get]
  rfl

/-- A packed node record can be mounted as a middle segment of the diagonal bit stream.
Subsequent root records and all earlier packed public tables stay in their original order. -/
theorem mount_tape (a : NodeArchive) (rows : List Layers) (m : Memory W) (base : ℕ)
    (before after : List ℕ) (offset : a.rawHeader=base+W*before.length)
    (phase : a.phase<2^W) (apart : a.rawHeader+W*(16*rows.length)≤a.headerBase)
    (room : a.headerBase+16*rows.length<2^W)
    (bits : let v:=before++(nodeTape a.banks a.headerBase rows++after)
      ∀ k<v.length,∀ j<W,m (base+W*k+j)=(((v[k]?.getD 0:Word W).val.testBit (W-1-j)).toNat:Word W)) :
    Mount (image a rows.length) (tapeWord a rows) m := by
  have src : (image a rows.length).source m=a.rawHeader := by unfold PackedStageArchive.Layout.source;change (if _ then a.rawHeader else a.rawHeader)=a.rawHeader;simp
  refine ⟨phase,by rw [src];exact apart,room,?_⟩
  intro i hi j hj
  change i<16*rows.length at hi
  have hit : i<(nodeTape a.banks a.headerBase rows).length := by simpa using hi
  have all:=bits (before.length+i) (by simp;omega) j hj
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_append_left hit] at all
  have addr : a.rawHeader+W*i+j=base+W*(before.length+i)+j := by rw [offset,Nat.mul_add];omega
  rw [src,addr]
  simpa only [image,tapeWord,Nat.add_sub_cancel_left] using all

def stable (a : NodeArchive) (rows : List Layers) (x : ℕ) : Prop :=
  x≠a.counter ∧ x≠a.banks.current ∧ outside a.headerBase (16*rows.length) x ∧
    ∀ i : Fin rows.length, keeps a (rows.get i) x

/-- An input cell off all output segments has its original value, even during the
decrement at the start of a layer. This applies to raw input bits and row/motif data. -/
theorem input_read (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (i : Fin rows.length) (x : ℕ) (off : stable a rows x) :
    decrement a (state a P m i.val) x=m x := by
  have h:=state_keeps a P m x 0 i.val (Nat.zero_le _) i.isLt.le room.counterSize room.pointerSize
    (fun j _ _=>off.2.2.2 j)
  simp only [decrement,writeMemory,Fin.val_cast_of_lt room.counterSize,ite_eq_right off.1]
  rw [h]
  simp only [state,initial,writeMemory,Fin.val_cast_of_lt room.counterSize,Fin.val_cast_of_lt room.pointerSize,
    ite_eq_right off.1,ite_eq_right off.2.1]
  exact segment_keeps _ _ _ _ _ off.2.2.1

theorem state_current (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (k : ℕ) (bound : k≤rows.length) :
    state a P m k a.banks.current=(hdr a k:Word W) := by
  cases k with
  | zero =>
    simp [state,initial,writeMemory,Fin.val_cast_of_lt room.counterSize,Fin.val_cast_of_lt room.pointerSize,
      Ne.symm room.controls,hdr]
  | succ k =>
    let i : Fin rows.length := ⟨k,by omega⟩
    rw [show k+1=i.val+1 by rfl,state_step]
    simp only [nextState,emitted,writeMemory,Fin.val_cast_of_lt room.pointerSize,ite_true]

structure TapeBounds (W : ℕ) (a : NodeArchive) (rows : List Layers) : Prop where
  control : a.banks.current<a.headerBase
  counter : a.counter<a.headerBase
  endHeader : a.headerBase+16*rows.length≤a.banks.charges
  fields : ∀ (i : Fin rows.length) (j : Fin 14),
    header a.banks (rows.get i).actual (rows.get i).parent (hdr a (i.val+1)) j.val<2^W

theorem stage_mounted (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (tape : TapeBounds W a rows) (i : Fin rows.length) :
    Mounted a.banks (rows.get i).actual (rows.get i).parent (hdr a i.val) (hdr a (i.val+1))
      (decrement a (state a P m i.val)) := by
  have hdrfit : hdr a i.val<2^W := by
    have p := (room.layer i).header
    have q := (room.layer i).chargeEnd
    have z := (room.layer i).nodeEnd
    omega
  constructor
  · simp only [decrement,writeMemory,Fin.val_cast_of_lt room.counterSize,ite_eq_right (Ne.symm room.controls),
      state_current a P m room i.val i.isLt.le,Fin.val_cast_of_lt hdrfit]
  · intro j hj
    let x:=hdr a i.val+j
    have low : a.headerBase≤x := by dsimp [x,hdr];omega
    have high : x<a.headerBase+16*rows.length := by dsimp [x,hdr];have:=i.isLt;omega
    have left : x≠a.counter := by have:=tape.counter;omega
    have right : x≠a.banks.current := by have:=tape.control;omega
    have old : state a P m i.val x = state a P m 0 x := by
      apply state_keeps a P m x 0 i.val (Nat.zero_le _) i.isLt.le room.counterSize room.pointerSize
      intro l _ _
      have b:=tape.endHeader
      have c:=(room.layer l).chargeEnd
      exact ⟨left,right,.inl (by omega),.inl (by omega)⟩
    have read := tapeWord_read (W:=W) a i (⟨j,by omega⟩:Fin 16)
    change (decrement a (state a P m i.val) x).val=_
    simp only [decrement,writeMemory,Fin.val_cast_of_lt room.counterSize,ite_eq_right left,old,state,initial,
      Fin.val_cast_of_lt room.pointerSize,ite_eq_right right,fillSegment,ite_eq_left (And.intro low high)]
    exact (congrArg Fin.val read).trans (Fin.val_cast_of_lt (tape.fields i ⟨j,hj⟩))

/-- Physical input data read once before the archive pass, together with their actual
addresses. Indirect lookups may occur in the seed arena above the output banks. -/
structure SourceRows (a : NodeArchive) (P : Program rows) (m : Memory W) : Prop where
  reads : ∀ i, (P.data i).Reads (natural m)
  bounds : ∀ i, (P.data i).Below (2^W) (natural m)
  input : ∀ i, (P.data i).Footprint (stable a rows) (natural m)
  separate : ∀ i, (P.data i).Footprint (fun x=>x<a.banks.charges ∨
    a.banks.nodes+8*((rows.get i).actual.first+(rows.get i).actual.count)≤x) (natural m)
  owners : ∀ i, ParentReads (rows.get i).parent (P.owners i) (natural m)
  parentCells : ∀ (i : Fin rows.length), (rows.get i).parent.finalLayer=false →
    ∀ j : Fin (rows.get i).actual.count, stable a rows ((rows.get i).parent.owners+j.val)
  preceding : ∀ i j k,(P.data i).child j k<(rows.get i).actual.first
  halves : ∀ i j, ((P.data i).halfWidth j).length≤a.halfCap
  motifs : ∀ i,(rows.get i).actual.kind≠0 → ∀ j,((P.data i).motifCopies j).length≤a.motifCap

theorem ready_of_source (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (tape : TapeBounds W a rows) (src : SourceRows a P m)
    (pairs : ∀ i j, (P.data i).cost a.banks (prior a (decrement a (state a P m i.val))) j 1<2^W)
    (i : Fin rows.length) : bodyReady a P m i := by
  let dec:=decrement a (state a P m i.val)
  have same (x : ℕ) (off : stable a rows x) : natural dec x = natural m x :=
    congrArg Fin.val (input_read a P m room i x off)
  refine ⟨stage_mounted a P m room tape i,(src.reads i).of_footprint (src.input i) same,
    (src.bounds i).of_footprint (src.input i) same,(src.separate i).transfer (src.input i) same,?_,
    src.preceding i,fun _ _ _=>rfl,src.halves i,src.motifs i,pairs i⟩
  intro final j
  exact (same _ (src.parentCells i final j)).trans (src.owners i final j)

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open scoped Fin.CommRing Classical BigOperators
variable {W : ℕ} {rows : List Layers}

def Chronological (rows : List Layers) : Prop :=
  ∀ i k : Fin rows.length, i<k →
    (rows.get i).actual.first+(rows.get i).actual.count≤(rows.get k).actual.first

private theorem oldCharge_keeps (a : NodeArchive) (i : Fin rows.length) {budget : ℕ}
    (room : RunBounds W a rows budget) (id : ℕ) (before : id<(rows.get i).actual.first) (col : Fin 2) :
    keeps a (rows.get i) (a.banks.charges+2*id+col.val) := by
  have c:=room.counter
  have ctl:=(room.layer i).current
  have split:=(room.layer i).chargeEnd
  have small:=col.isLt
  exact ⟨by omega,by omega,.inl (by omega),.inl (by omega)⟩

private theorem oldNode_keeps (a : NodeArchive) (i : Fin rows.length) {budget : ℕ}
    (room : RunBounds W a rows budget) (id : ℕ) (before : id<(rows.get i).actual.first) (col : Fin 8) :
    keeps a (rows.get i) (a.banks.nodes+8*id+col.val) := by
  have c:=room.counter
  have ctl:=(room.layer i).current
  have split:=(room.layer i).chargeEnd
  have small:=col.isLt
  exact ⟨by omega,by omega,.inr (by omega),.inl (by omega)⟩

theorem charge_word_at (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (ordered : Chronological rows) (i : Fin rows.length)
    (j : Fin (rows.get i).actual.count) (c : Fin 2) (t : ℕ) (after : i.val<t) (ht : t≤rows.length) :
    state a P m t (a.banks.charges+2*((rows.get i).actual.first+j.val)+c.val) =
      ((P.data i).cost a.banks (prior a (decrement a (state a P m i.val))) j c:Word W) := by
  let loc:=a.banks.charges+2*((rows.get i).actual.first+j.val)+c.val
  have keep : state a P m t loc=state a P m (i.val+1) loc := by
    apply state_keeps a P m loc (i.val+1) t after ht room.counterSize room.pointerSize
    intro k h _
    have end':=(ordered i k (show i<k from h))
    apply oldCharge_keeps a k room _ _ c
    have bound:=j.isLt
    omega
  rw [keep,state_step]
  exact emitted_charge (room.layer i) j c

theorem before_charge (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (ordered : Chronological rows) (i t : Fin rows.length) (lt : i<t)
    (j : Fin (rows.get i).actual.count) (c : Fin 2) :
    prior a (decrement a (state a P m t.val)) ((rows.get i).actual.first+j.val) c =
      (((P.data i).cost a.banks (prior a (decrement a (state a P m i.val))) j c : Word W)).val := by
  have read:=charge_word_at a P m room ordered i j c t.val lt t.isLt.le
  have ne : a.banks.charges+2*((rows.get i).actual.first+j.val)+c.val≠a.counter := by
    have :=room.counter;omega
  simpa only [prior,decrement,writeMemory,Fin.val_cast_of_lt room.counterSize,ite_eq_right ne] using congrArg Fin.val read

theorem final_charge_word (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (ordered : Chronological rows) (i : Fin rows.length)
    (j : Fin (rows.get i).actual.count) (c : Fin 2) :
    state a P m rows.length (a.banks.charges+2*((rows.get i).actual.first+j.val)+c.val) =
      ((P.data i).cost a.banks (prior a (decrement a (state a P m i.val))) j c:Word W) :=
  charge_word_at a P m room ordered i j c rows.length i.isLt le_rfl

theorem final_node_word (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (ordered : Chronological rows) (i : Fin rows.length)
    (j : Fin (rows.get i).actual.count) (c : Fin 8) :
    state a P m rows.length (a.banks.nodes+8*((rows.get i).actual.first+j.val)+c.val) =
      ((LayerRecord a.banks (rows.get i).actual (rows.get i).parent (P.owners i)
        ((P.data i).cost a.banks (prior a (decrement a (state a P m i.val)))) j).words c:Word W) := by
  let loc:=a.banks.nodes+8*((rows.get i).actual.first+j.val)+c.val
  have keep : state a P m rows.length loc=state a P m (i.val+1) loc := by
    apply state_keeps a P m loc (i.val+1) rows.length i.isLt le_rfl room.counterSize room.pointerSize
    intro k h _
    have end':=ordered i k (show i<k from h)
    apply oldNode_keeps a k room _ _ c
    have bound:=j.isLt
    omega
  rw [keep,state_step]
  exact emitted_node (room.layer i) j c

/-- Both sides of the unrolled recurrence use words in the final physical memory. -/
theorem final_charge (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (ordered : Chronological rows) (i : Fin rows.length)
    (j : Fin (rows.get i).actual.count) (col : Fin 2)
    (old : ∀ k,(P.data i).child j k<(rows.get i).actual.first)
    (fits : (P.data i).cost a.banks (prior a (decrement a (state a P m i.val))) j col<2^W) :
    prior a (state a P m rows.length) ((rows.get i).actual.first+j.val) col =
      (P.data i).cost a.banks (prior a (state a P m rows.length)) j col := by
  have atRow := (congrArg Fin.val (final_charge_word a P m room ordered i j col)).trans (Fin.val_cast_of_lt fits)
  change (state a P m rows.length _).val=_
  rw [atRow]
  dsimp only [LayerData.cost]
  apply congrArg₂ Nat.add rfl
  apply Finset.sum_congr rfl
  intro k _
  let id:=(P.data i).child j k
  let x:=a.banks.charges+2*id+col.val
  have keep : state a P m rows.length x=state a P m i.val x := by
    apply state_keeps a P m x i.val rows.length i.isLt.le le_rfl room.counterSize room.pointerSize
    intro t le _
    apply oldCharge_keeps a t room id _ col
    by_cases eq : i=t
    · subst t; exact old k
    · have less : i<t:=lt_of_le_of_ne (show i≤t from le) eq
      have end':=ordered i t less
      exact (old k).trans_le (by omega)
  have off : x≠a.counter := by dsimp [x];have:=room.counter;omega
  change (decrement a (state a P m i.val) x).val=(state a P m rows.length x).val
  simp only [decrement,writeMemory,Fin.val_cast_of_lt room.counterSize,ite_eq_right off,keep]

theorem final_parent_word (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (ordered : Chronological rows) (i : Fin rows.length)
    (j : Fin (rows.get i).actual.count) :
    state a P m rows.length (a.banks.nodes+8*((rows.get i).actual.first+j.val)+1) =
      ((if (rows.get i).parent.finalLayer then (rows.get i).actual.first+j.val
        else (rows.get i).parent.first+P.owners i j:ℕ):Word W) :=
  final_node_word a P m room ordered i j (1:Fin 8)

theorem final_input (a : NodeArchive) (P : Program rows) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a rows budget) (x : ℕ) (off : stable a rows x) :
    state a P m rows.length x=m x := by
  rw [state_keeps a P m x 0 rows.length (Nat.zero_le _) le_rfl room.counterSize room.pointerSize
    (fun i _ _=>off.2.2.2 i)]
  simp only [state,initial,writeMemory,Fin.val_cast_of_lt room.counterSize,Fin.val_cast_of_lt room.pointerSize,
    ite_eq_right off.1,ite_eq_right off.2.1]
  exact segment_keeps _ _ _ _ _ off.2.2.1

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
