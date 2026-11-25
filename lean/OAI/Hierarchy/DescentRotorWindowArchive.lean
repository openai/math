import OAI.Hierarchy.DescentRotorWindowSize
import OAI.Hierarchy.DescentRotorWindowTicketRead
import OAI.Hierarchy.DescentReservationHeader
import OAI.Hierarchy.DescentPackedRotorMatrix
import OAI.Hierarchy.DescentPackedReservationColumn
import OAI.Hierarchy.DescentFallbackPeriodRun

namespace OAI
/-! # One chronological gather of old signed words, inverse GL comparisons and shared host data -/
namespace Hierarchy.DescentRotorWindowArchive
open DescentSIMDLookup DescentFallbackPeriod DescentPackedFallbackTree.Image DescentPackedZip
open DescentPacking.PackedMatch.Local.Gather DescentRotorWindowScore
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r field H G w M : ℕ}

/-- One roster's geometry is reused for every old donor and every signed grain. -/
abbrev Old (D L cap : ℕ) := (Fin L ⊕ Fin D×Fin L) ⊕ (Fin L×Fin (2*cap))
abbrev Input (D L cap : ℕ) := Old D L cap ⊕ ((Fin L×Fin L) ⊕ (Fin D×(Fin D×Fin 6)))
def ix : Input D L cap ≃ Fin (count D L cap) :=
  let old:=((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)
  let mark:=(Equiv.sumCongr old finProdFinEquiv).trans finSumFinEquiv
  let peers:=(Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv
  (Equiv.sumCongr mark ((Equiv.sumCongr finProdFinEquiv peers).trans finSumFinEquiv)).trans finSumFinEquiv

abbrev RowData (D L cap field : ℕ) := Input D L cap→Cell field
def source (x : RowData D L cap field) : Packet D L cap n r field
  | .inl u=>x (.inl (.inl u))
  | .inr (.inl u)=>x (.inl (.inr u))
  | .inr (.inr _)=>0

def orderField (x : RowData D L cap field) (i j : Fin L) := decide ((x (.inr (.inl (i,j)))).val=1)
def metadata (x : RowData D L cap field) (p j : Fin D) (a : Fin 6) := x (.inr (.inr (p,j,a)))

def observed (v : Packet D L cap n r field) (x : Fin L→Fin L→Bool) (y : Fin D→Fin D→Fin 6→Cell field) :
    RowData D L cap field
  | .inl (.inl u)=>v (.inl u)
  | .inl (.inr u)=>v (.inr (.inl u))
  | .inr (.inl (i,j))=>(x i j).toNat
  | .inr (.inr (p,j,a))=>y p j a

theorem observed_reads (v : Packet D L cap n r field) (x : Fin L→Fin L→Bool)
    (y : Fin D→Fin D→Fin 6→Cell field) (pos : 0<field) :
    let a:=observed v x y
    orderField a=x ∧ metadata a=y ∧
    (∀j s,entry (n:=n) (r:=r) (source a) s j=entry v s j) := by
  refine ⟨?_,rfl,fun _ _=>rfl⟩
  funext i j
  cases eqn : x i j <;> simp [orderField,observed,eqn,pos]

def fieldRow (x : RowData D L cap field) (s : Bool) (j : Slot L cap) (candidate : Fin D)
    (a : Entry) : Fin (DescentPackedReservationColumn.fields D)→Cell field := fun id=>
  match finSumFinEquiv.symm id with
  | .inl z=>
    let tally:=DescentRotorWindowScore.tally (n:=n) (r:=r) (source x) s (orderField x) j
    let span:=(metadata x candidate candidate 1).val
    (![a.ownBase/2^r,a.ownBase%2^r,a.peerBase%2^r,tally%span] z:ℕ)
  | .inr z=>
    let f:=finProdFinEquiv.symm z
    metadata x candidate f.1 f.2

theorem row_request (x : RowData D L cap field) (s : Bool) (j : Slot L cap) (peer : Fin D) (e : Entry) (q : Fin 4) :
    fieldRow (n:=n) (r:=r) x s j peer e (DescentPackedReservationColumn.request q)=
      (![e.ownBase/2^r,e.ownBase%2^r,e.peerBase%2^r,
        DescentRotorWindowScore.tally (n:=n) (r:=r) (source x) s (orderField x) j%(metadata x peer peer 1).val] q : ℕ) := by
  simp [fieldRow,DescentPackedReservationColumn.request]

theorem row_neighbor (x : RowData D L cap field) (s : Bool) (j : Slot L cap) (peer other : Fin D) (e : Entry) (q : Fin 6) :
    fieldRow (n:=n) (r:=r) x s j peer e (DescentPackedReservationColumn.neighbor other q)=metadata x peer other q := by
  simp [fieldRow,DescentPackedReservationColumn.neighbor]

theorem observed_tally (v : Packet D L cap n r field) (ord : Fin L→Fin L→Bool)
    (y : Fin D→Fin D→Fin 6→Cell field) (h : 0<field) (s : Bool) (j : Slot L cap) :
    let x:=observed v ord y
    DescentRotorWindowScore.tally (n:=n) (r:=r) (source x) s (orderField x) j=
      DescentRotorWindowScore.tally v s ord j := by
  have read:=observed_reads v ord y h
  simp only [DescentRotorWindowScore.tally,read.1,read.2.2]

def pairCode (s : Bool) (root : ℕ×ℕ) (x : RowData D L cap field) (j : Slot L cap) : Cell (DescentPackedRotorMatrix.bits n) := Id.run do
  let v:Packet D L cap n r field:=source x
  let some a:=entry v s j | return 0
  let some p:=DescentFallbackPeriod.arrival v s j.1 j.2 | return 0
  let slots:=DescentPackedReservationColumn.fields D
  let row:=fieldRow (n:=n) (r:=r) x s j p.1 a
  let col:=DescentPackedReservationColumn.column n D field (2^r) (encode field slots row)
  return DescentPackedRotorMatrix.signedPair r n root (localWord v j.1) p.2 col.val

theorem pairCode_none (side : Bool) (root : ℕ×ℕ) (x : RowData D L cap field) (j : Slot L cap)
    (ghost : entry (n:=n) (r:=r) (source x) side j=none) : pairCode (r:=r) (n:=n) side root x j=0 := by
  simp [pairCode,ghost]

theorem pairCode_some (side : Bool) (root : ℕ×ℕ) (x : RowData D L cap field) (j : Slot L cap)
    (a : Entry) (p : Fin D×ℕ) (live : entry (n:=n) (r:=r) (source x) side j=some a)
    (arrived : DescentFallbackPeriod.arrival (n:=n) (r:=r) (source x) side j.1 j.2=some p) :
    pairCode (r:=r) side root x j=DescentPackedRotorMatrix.signedPair r n root (localWord (n:=n) (r:=r) (source x) j.1) p.2
      (DescentPackedReservationColumn.column n D field (2^r) (encode field _
        (fieldRow (r:=r) (n:=n) x side j p.1 a))).val := by
  simp [pairCode,live,arrived]

def matrix (r n : ℕ) (side : Bool) (root : ℕ×ℕ) (x : RowData D L cap field) :=
  DescentPackedRotorMatrix.tally n (L*(2*cap))
    (DescentPackedRotorMatrix.rows n (L*(2*cap)) (fun i=>pairCode (r:=r) side root x (finProdFinEquiv.symm i)))

def pack (x : RowData D L cap field) := encode field (count D L cap) (fun j=>x (ix.symm j))
def output (n L cap : ℕ) := DescentPackedRotorMatrix.bins (L*(2*cap))*((2^n)*(2^n))
def law (r n : ℕ) (side : Bool) (root : ℕ×ℕ) (packed : Cell (field*count D L cap)) : Cell (output n L cap) :=
  matrix r n side root (fun j=>(encode field (count D L cap)).symm packed (ix j))

theorem law_read (side : Bool) (root : ℕ×ℕ) (x : RowData D L cap field) :
    law r n side root (pack x)=matrix r n side root x := by
  simp [law,pack]
  rfl

theorem gatheredMap {b : ℕ} (emit : Cell (output n L cap)→Cell b) (side : Bool) (root : ℕ×ℕ) (tables : Fin (count D L cap)→Tables)
    (reads : Fin (count D L cap)→Expr) (menu : DescentSIMDLookup.Banks) (mid out : ℕ)
    (x : Fin H→Fin G→RowData D L cap field) (pos : 0<M) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M m)
    (sources : ∀j,Source (reads (ix j)) (fun a g=>x a g j) M m)
    (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*count D L cap) b M H G w out)
    (rom : resident (emit ∘ law (D:=D) (L:=L) (cap:=cap) (field:=field) r n side root) menu H G M m)
    (dictLow : menu.dictionary.base+2^((field*count D L cap)*M)≤ mid)
    (maskLow : menu.mask.base+H*chunks G M≤ mid) (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act m)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec m dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit b (lane g pos).val (dst (out+(row H G M (position a g pos)).val)).val=
       (emit (matrix r n side root (x a g))).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=m addr := by
  let act:=assembly tables reads
  let rows:=H*chunks G M
  let middle:=image mid rows act m
  let fn:=emit ∘ law (D:=D) (L:=L) (cap:=cap) (field:=field) r n side root
  have old (a : ℕ) (below : a< mid) : middle a=m a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl below)
  have fixed : resident fn menu H G M middle := by
    refine ⟨fun i=>?_,fun i=>?_⟩
    · rw [old _ (by have:=i.isLt;omega)];exact rom.1 i
    · rw [old _ (by have:=i.isLt;omega)];exact rom.2 i
  have slots (j):=sources (ix.symm j)
  have seen:=collected tables reads mid bounds m constants (fun a g j=>x a g (ix.symm j))
    (fun j=>by simpa using slots j) (List.finRange _)
  have input (p : Row H G M) : middle (menu.source.base+(row H G M p).val)=(data (fun v j=>pack (x v j)) p).val := by
    rw [wire]
    apply (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans
    simpa only [pack,act,assembly,List.mem_finRange,ite_true] using seen p
  have gather : (scan w mid rows act).Exec m middle (4+rows*(2*act.work+4)) :=
    @ProtocolRAM.scan_exec w mid rows act m
      (DescentPacking.PackedMatch.Local.Gather.fits tables reads mid bounds (List.finRange _)) room
  obtain ⟨run,read,_⟩:=DescentPackedLocalLookup.compile menu out fn (fun v j=>pack (x v j)) pos fit middle fixed input
  refine ⟨gather.then run,fun a g=>(read a g).trans (congrArg (fun t=>(emit t).val) (law_read ..)),?_⟩
  intro addr awayMid awayOut
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ awayOut).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ awayMid)

theorem gathered (side : Bool) (root : ℕ×ℕ) (tables : Fin (count D L cap)→Tables)
    (reads : Fin (count D L cap)→Expr) (menu : DescentSIMDLookup.Banks) (mid out : ℕ)
    (x : Fin H→Fin G→RowData D L cap field) (pos : 0<M) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M m)
    (sources : ∀j,Source (reads (ix j)) (fun a g=>x a g j) M m)
    (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*count D L cap) (output n L cap) M H G w out)
    (rom : resident (law (D:=D) (L:=L) (cap:=cap) (field:=field) r n side root) menu H G M m)
    (dictLow : menu.dictionary.base+2^((field*count D L cap)*M)≤ mid)
    (maskLow : menu.mask.base+H*chunks G M≤ mid) (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act m)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec m dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit (output n L cap) (lane g pos).val (dst (out+(row H G M (position a g pos)).val)).val=
       (matrix r n side root (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=m addr := by
  exact gatheredMap (r:=r) id side root tables reads menu mid out x pos m bounds constants sources room fit rom dictLow maskLow wire

end
end Hierarchy.DescentRotorWindowArchive

end OAI
