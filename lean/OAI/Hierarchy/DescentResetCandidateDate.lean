import OAI.Hierarchy.DescentResetCandidateShape
import OAI.Hierarchy.DescentResetCandidateBatch
import OAI.Hierarchy.DescentRelativeRank
import OAI.Hierarchy.DescentResetJoinedRank
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # A mounted four-peer rank or seven-field candidate publication at one public date -/
namespace Hierarchy.DescentResetCandidateDate
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentPackedFallbackTree.Image DescentOrdinaryAtomFieldRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {N field b w : ℕ}
namespace Shape
variable (L : Shape)
def index (N : ℕ) : ((Fin N×Fin 2)⊕Fin 2)≃Fin (N*2+2) := ((finProdFinEquiv).sumCongr (Equiv.refl _)).trans finSumFinEquiv

def dict (emit : (Fin N→Cell field)→Cell b) : ROM.Page :=
  ⟨(field*N)*L.lanes,fun i=>(DescentSIMDLookup.table (emit ∘ (encode field N).symm) i).val⟩
def mask (b : ℕ) : ROM.Page :=
  ⟨L.rowBits,fun i=>if inside : i.val<L.rows then maskWord b L.lanes L.groups
    ((row L.hosts L.groups L.lanes).symm ⟨i.val,inside⟩).2.val else 0⟩

def pages (emit : (Fin N→Cell field)→Cell b) (i : Fin (N*2+2)) : ROM.Page :=
  ((index N).symm i).elim (fun k=>ROM.binary (setField (d:=field) k.1) L.lanes k.2)
    (fun z=>if z=0 then L.dict emit else L.mask b)
def bank (emit : (Fin N→Cell field)→Cell b) (j : Fin (N*2+2)) :=
  ROM.bank (L.pages emit) (L.width N field) L.first j
def tables (emit : (Fin N→Cell field)→Cell b) (i : Fin N) :=
  ROM.joined (L.pages emit) (L.width N field) L.first (fun d=>index N (.inl (i,d)))
def menu (emit : (Fin N→Cell field)→Cell b) : DescentSIMDLookup.Banks :=
  ⟨⟨L.scratch N field,L.rowBits⟩,L.bank emit (index N (.inr 0)),L.bank emit (index N (.inr 1))⟩
def output (N field : ℕ) (j : ℕ) : Bank:=⟨DescentResetCandidateBatch.slab (L.base N field) L.stride j,L.rowBits⟩

def mounted (emit : (Fin N→Cell field)→Cell b) (m : Memory w) :=
  ROM.after (L.pages emit) (L.width N field) L.first m
def setup (emit : (Fin N→Cell field)→Cell b) (w : ℕ) :=
  ROM.mount (L.pages emit) (L.width N field) w L.first
def op (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr) (j : ℕ) :=
  assembly (L.tables emit) (reads j)
def code (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr) (w : ℕ) :=
  (L.setup emit w).seq (DescentResetCandidateBatch.program
    (DescentResetCandidateBatch.stepCode w (L.scratch N field) L.rows (L.op emit reads) (L.base N field) L.stride (L.menu emit))
    0 L.jobs)
def image (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr) (m : Memory w) :=
  DescentResetCandidateBatch.result
    (DescentResetCandidateBatch.stepImage (L.scratch N field) L.rows (L.op emit reads) (L.base N field) L.stride (L.menu emit))
    0 L.jobs (L.mounted emit m)
def ticks (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr) :=
  (4+10*L.size N field)+DescentResetCandidateBatch.clock (DescentResetCandidateBatch.time L.rows (L.op emit reads)) 0 L.jobs

theorem rows_fit : L.rows≤L.stride:=Nat.le_pow_clog (by decide) _
theorem ordered (N field : ℕ) : L.first≤L.scratch N field ∧ L.scratch N field+L.rows≤L.base N field ∧ L.base N field≤L.endAddress N field :=
  ⟨Nat.le_add_right ..,Nat.add_le_add_left L.rows_fit _,Nat.le_add_right ..⟩
theorem page_size (emit : (Fin N→Cell field)→Cell b) (j : Fin (N*2+2)) :
    (L.pages emit j).bits≤L.width N field := by
  obtain ⟨tag,rfl⟩:=(index N).surjective j
  rcases tag with ⟨i,k⟩|k
  · simp only [pages,Equiv.symm_apply_apply,Sum.elim_inl]
    fin_cases k
    · exact (Nat.mul_le_mul_right L.lanes (Nat.le_add_right _ _)).trans (le_max_left ..)
    · exact le_max_left ..
  · simp only [pages,Equiv.symm_apply_apply,Sum.elim_inr]
    split
    · exact (Nat.mul_le_mul_right L.lanes (Nat.le_add_right _ _)).trans (le_max_left ..)
    · exact le_max_right ..

theorem page_room (emit : (Fin N→Cell field)→Cell b) (j : Fin (N*2+2)) (room : L.endAddress N field<2^w) :
    (L.bank emit j).Fits w (L.scratch N field):=
  ROM.bank_room _ _ _ _ j (L.page_size emit j) le_rfl
    ((Nat.le_add_right _ L.rows).trans ((L.ordered N field).2.1.trans (L.ordered N field).2.2) |>.trans_lt room)

theorem bounds (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr)
    (prior : ∀j<L.jobs,∀i,(reads j i).Fits w L.first) (room : L.endAddress N field<2^w) (j : ℕ) (hj : j<L.jobs) :
    Bounds (w:=w) (d:=field) (M:=L.lanes) (L.tables emit) (reads j) (L.scratch N field) := by
  intro i
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ (L.ordered N field).1 (prior j hj i),L.page_room emit _ room,L.page_room emit _ room,?_,?_⟩
  · simp [tables,ROM.joined,ROM.bank,pages,ROM.binary]
  · simp [tables,ROM.joined,ROM.bank,pages,ROM.binary]

theorem lookup_fits (emit : (Fin N→Cell field)→Cell b) (j : ℕ)
    (room : L.endAddress N field<2^w) : (lookup (L.menu emit)).Fits w (L.output N field j).base := by
  have sep : L.scratch N field≤(L.output N field j).base:=by dsimp [output,DescentResetCandidateBatch.slab,base];omega
  have srcFit : (L.menu emit).source.Fits w (L.output N field j).base:=by
    change 0<L.stride ∧ L.stride<2^w ∧ L.scratch N field+L.stride≤L.base N field+j*L.stride
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((L.ordered N field).2.2.trans_lt room),Nat.le_add_right ..⟩
  have grow {x : Bank} (h : x.Fits w (L.scratch N field)) : x.Fits w (L.output N field j).base:=
    ⟨h.1,h.2.1,h.2.2.trans sep⟩
  exact ⟨⟨grow (L.page_room emit _ room),srcFit,trivial⟩,grow (L.page_room emit _ room),trivial⟩

theorem any (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr)
    (m : Memory w) (prior : ∀j<L.jobs,∀i,(reads j i).Fits w L.first) (room : L.endAddress N field<2^w) :
    (L.code emit reads w).Exec m (L.image emit reads m) (L.ticks emit reads) ∧ CheapCode (L.code emit reads w) ∧
      ∀a,a<L.first ∨ L.endAddress N field≤a→L.image emit reads m a=m a := by
  let act:=L.op emit reads
  obtain ⟨early,gap,ceil⟩:=L.ordered N field
  have lower:=(Nat.le_add_right (L.scratch N field) L.rows).trans gap
  have small:=lower.trans_lt (ceil.trans_lt room)
  have mount:=ROM.run (L.pages emit) (L.width N field) L.first m small
  have go:=DescentResetCandidateBatch.any (L.scratch N field) L.rows (L.base N field) L.stride 0 L.jobs act (L.menu emit)
    (L.mounted emit m) gap L.rows_fit (gap.trans_lt (ceil.trans_lt room))
    (fun j _ hj=>DescentPacking.PackedMatch.Local.Gather.fits _ _ _ (L.bounds emit reads prior room j (by omega)) _)
    (fun j _ _=>L.lookup_fits emit j room) (by simpa [DescentResetCandidateBatch.slab,endAddress] using room)
  refine ⟨Procedure.Exec.then (A:=L.setup emit w) mount.1 go.1,?_,?_⟩
  · exact cheap_seq (@ROM.cheap _ (L.pages emit) (L.width N field) w L.first)
      (@DescentResetCandidateBatch.cheap w (L.scratch N field) L.rows (L.base N field)
        L.stride act (L.menu emit) 0 L.jobs)
  intro a away
  apply (go.2 a ?_ ?_).trans (ROM.frame _ _ _ m a (by rcases away with low|high;exact .inl low;exact .inr (lower.trans (ceil.trans high))))
  · rcases away with low|high
    · exact .inl (low.trans_le early)
    · exact .inr (gap.trans (ceil.trans high))
  · simpa [DescentResetCandidateBatch.slab,endAddress] using
      away.imp (fun low=>low.trans_le (early.trans lower)) id

theorem books (emit : (Fin N→Cell field)→Cell b) (m : Memory w) :
    (∀i,Static (L.tables emit i) (setField (d:=field) i) L.lanes (L.mounted emit m)) ∧
      resident (emit ∘ (encode field N).symm) (L.menu emit) L.hosts L.groups L.lanes (L.mounted emit m) := by
  have number_eq {P Q : ROM.Page} (same : P=Q) {n : ℕ} (p : n<2^P.bits) (q : n<2^Q.bits) :
      P.number ⟨n,p⟩=Q.number ⟨n,q⟩ := by cases same; rfl
  refine ⟨fun i=>ROM.binary_mounted _ _ _ _ _ m (L.page_size emit) (fun k=>index N (.inl (i,k))) ?_,?_⟩
  · intro k;simp [pages]
  · constructor
    · intro i
      change L.mounted emit m ((L.bank emit (index N (.inr 0))).base+i.val)=_
      have bound : i.val<2^((L.pages emit (index N (.inr 0))).bits):=by simp [pages,dict]
      have same : L.pages emit (index N (.inr 0))=L.dict emit := by simp [pages]
      apply (ROM.read (L.pages emit) (L.width N field) L.first m
        (index N (.inr 0)) (L.page_size emit _) ⟨i.val,bound⟩).trans
      exact congrArg (fun n : ℕ=>(n:Word w)) (number_eq same bound i.isLt)
    · intro i
      change L.mounted emit m ((L.bank emit (index N (.inr 1))).base+i.val)=_
      have small : i.val<2^L.rowBits:=i.isLt.trans_le L.rows_fit
      have bound : i.val<2^((L.pages emit (index N (.inr 1))).bits):=by simpa [pages,mask] using small
      have same : L.pages emit (index N (.inr 1))=L.mask b := by simp [pages]
      have inside : i.val<L.rows := i.isLt
      apply (ROM.read (L.pages emit) (L.width N field) L.first m
        (index N (.inr 1)) (L.page_size emit _) ⟨i.val,bound⟩).trans
      apply (congrArg (fun n : ℕ=>(n:Word w)) (number_eq same bound small)).trans
      simp only [mask,dite_eq_left inside]

theorem output_fits {N field} (j : ℕ) (ok : j<L.jobs) (room : L.endAddress N field<2^w) :
    (L.output N field j).Fits w (L.endAddress N field) := by
  have grow:=Nat.mul_le_mul_right L.stride ok
  rw [Nat.succ_mul] at grow
  change 0<L.stride ∧ L.stride<2^w ∧ (L.base N field+j*L.stride)+L.stride≤L.base N field+L.jobs*L.stride
  have lo : L.stride≤L.base N field:=Nat.le_add_left ..
  exact ⟨Nat.two_pow_pos _,lo.trans_lt ((L.ordered N field).2.2.trans_lt room),by omega⟩

theorem fit (emit : (Fin N→Cell field)→Cell b) (j : ℕ) (ok : j<L.jobs)
    (room : L.endAddress N field<2^w) (packed : L.lanes*max (field*N) b≤w/2) :
    DescentSIMDLookup.Fits (L.menu emit) (field*N) b L.lanes L.hosts L.groups w (L.output N field j).base := by
  have prior:=L.lookup_fits (w:=w) emit j room
  have dst:=L.output_fits (N:=N) (field:=field) j ok room
  have last : (L.output N field j).base+L.rows<2^w:=
    ((Nat.add_le_add_left L.rows_fit _).trans dst.2.2).trans_lt room
  refine ⟨prior.1.2.1,prior.1.1,prior.2.1,L.rows_fit,?_,?_,last,packed⟩
  · simp [menu,bank,ROM.bank,pages,dict]
  · simpa [menu,bank,ROM.bank,pages,mask,Bank.size,stride,rows] using L.rows_fit

theorem words (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr)
    (m : Memory w) (prior : ∀j<L.jobs,∀i,(reads j i).Fits w L.first) (room : L.endAddress N field<2^w)
    (pos : 0<L.lanes) (packed : L.lanes*max (field*N) b≤w/2)
    (values : ℕ→Fin L.hosts→Fin L.groups→Fin N→Cell field)
    (inputs : ∀j<L.jobs,∀i,Source (reads j i) (fun v g=>values j v g i) L.lanes m) :
    ∀j<L.jobs,Source (.lookup (L.output N field j) .row)
      (fun v g=>emit (values j v g)) L.lanes (L.image emit reads m) := by
  obtain ⟨constants,rom⟩:=L.books emit m
  have geom (j) (hj : j<L.jobs):=L.fit emit j hj room packed
  obtain ⟨early,gap,ceil⟩:=L.ordered N field
  have bankLow (k : Fin (N*2+2)) : (L.bank emit k).base+(L.bank emit k).size≤L.scratch N field:=(L.page_room emit k room).2.2
  have dictLow : (L.menu emit).dictionary.base+2^((field*N)*L.lanes)≤L.scratch N field:=by
    simpa [menu,bank,ROM.bank,pages,dict,Bank.size] using bankLow (index N (.inr 0))
  have maskLow : (L.menu emit).mask.base+L.rows≤L.scratch N field:=by
    have span : L.rows≤(L.menu emit).mask.size:=by simpa [menu,bank,ROM.bank,pages,mask,Bank.size,stride] using L.rows_fit
    exact (Nat.add_le_add_left span _).trans (bankLow (index N (.inr 1)))
  have source (j) (hj : j<L.jobs) (k : Fin N) : Source (reads j k) (fun v g=>values j v g k) L.lanes (L.mounted emit m) := by
    intro r
    exact (eval_below _ _ m _ (prior j hj k) (fun a ha=>ROM.frame _ _ _ m a (.inl ha))).trans (inputs j hj k r)
  obtain ⟨_,all,_⟩:=DescentResetCandidateBatch.issue emit L.jobs (L.scratch N field) (L.base N field)
    L.stride (L.tables emit) reads (L.menu emit) values pos (L.mounted emit m)
    (L.bounds emit reads prior room) constants source (gap.trans_lt (ceil.trans_lt room)) gap L.rows_fit geom rom
    dictLow maskLow rfl
  intro j hj
  exact source_column _ _ (L.output_fits j hj room) _ _ L.rows_fit (all j hj)

theorem priced (emit : (Fin N→Cell field)→Cell b) (reads : ℕ→Fin N→Expr)
    (limit : ℕ) (work : ∀j<L.jobs,(L.op emit reads j).work≤limit) :
    L.ticks emit reads≤L.costBound N field limit ∧
    DescentStaticWordColumn.names (L.code emit reads w)≤L.nameBound N field limit := by
  have bounds : ∀j,0≤j→j<0+L.jobs→(L.op emit reads j).work≤limit:=fun j _ h=>work j (by simpa using h)
  refine ⟨Nat.add_le_add_left (DescentResetCandidateBatch.clock_le L.rows limit 0 L.jobs _ bounds) _,?_⟩
  unfold code
  rw [DescentStaticWordColumn.names_seq]
  change DescentStaticWordColumn.names (DescentStaticWordColumn.program w L.first _ (L.size N field))+_≤_
  rw [DescentStaticWordColumn.names_mount]
  exact Nat.add_le_add_left (DescentResetCandidateBatch.hardware _ _ _ _ _ _ 0 L.jobs limit bounds) _

end Shape

structure Mixed extends Shape where
  bits : ℕ
  rankReads : ℕ→Fin 5→Expr
  rawReads : ℕ→Fin 9→Expr
  rankOp : (Fin 5→Cell bits)→Cell bits := DescentRelativeClassChip.rank

namespace Mixed
variable (D : Mixed)
def ranks : Shape:={D.toShape with jobs:=3*D.jobs}
def masks : Shape:={D.toShape with first:=D.ranks.endAddress 5 D.bits}
def endAddress:=D.masks.endAddress 9 D.bits
def rankBank (j : ℕ) (c : Fin 3) := D.ranks.output 5 D.bits (3*j+c.val)
def fields (j : ℕ) (i : Fin 9) : Expr :=
  if use : 4≤ i.val ∧ i.val≤6 then .lookup (D.rankBank j ⟨i.val-4,by omega⟩) .row else D.rawReads j i
def code (w : ℕ) :=
  (D.ranks.code D.rankOp D.rankReads w).seq
    (D.masks.code (DescentCandidateMaskRAM.render (field:=D.bits)) D.fields w)
def image (m : Memory w) :=
  D.masks.image (DescentCandidateMaskRAM.render (field:=D.bits)) D.fields
    (D.ranks.image D.rankOp D.rankReads m)
def ticks :=
  D.ranks.ticks D.rankOp D.rankReads+
  D.masks.ticks (DescentCandidateMaskRAM.render (field:=D.bits)) D.fields
def output (j : ℕ) := D.masks.output 9 D.bits j

structure Previous (w : ℕ) : Prop where
  rank : ∀j<3*D.jobs,∀i,(D.rankReads j i).Fits w D.first
  raw : ∀j<D.jobs,∀i,(D.rawReads j i).Fits w D.first

theorem ordered : D.first≤D.masks.first ∧ D.masks.first≤D.endAddress := by
  have order (L : Shape) (N b : ℕ) : L.first≤L.endAddress N b:=
    (L.ordered N b).1.trans ((Nat.le_add_right _ L.rows).trans ((L.ordered N b).2.1.trans (L.ordered N b).2.2))
  exact ⟨order D.ranks 5 D.bits,order D.masks 9 D.bits⟩

theorem fieldFits (previous : D.Previous w) (room : D.endAddress<2^w) :
    ∀j<D.jobs,∀i,(D.fields j i).Fits w D.masks.first := by
  intro j inside i
  unfold fields
  split
  next use=>
    exact ⟨D.ranks.output_fits _ (by change 3*j+(i.val-4)<3*D.jobs;omega) (D.ordered.2.trans_lt room),trivial⟩
  next _=>exact ProtocolRAMGeneratedWrite.fits_mono _ D.ordered.1 (previous.raw j inside i)

theorem any (m : Memory w) (previous : D.Previous w) (room : D.endAddress<2^w) :
    (D.code w).Exec m (D.image m) D.ticks ∧ CheapCode (D.code w) ∧
    ∀a,a<D.first ∨ D.endAddress≤a→D.image m a=m a := by
  obtain ⟨early,endAt⟩:=D.ordered
  have step:=D.ranks.any D.rankOp D.rankReads m previous.rank (endAt.trans_lt room)
  have done:=D.masks.any (DescentCandidateMaskRAM.render (field:=D.bits)) D.fields
    (D.ranks.image D.rankOp D.rankReads m) (D.fieldFits previous room) room
  refine ⟨Procedure.Exec.then step.1 done.1,cheap_seq (@step.2.1) (@done.2.1),?_⟩
  intro a away
  exact (done.2.2 a (away.imp (fun h=>h.trans_le early) id)).trans
    (step.2.2 a (away.imp id (fun h=>endAt.trans h)))

/-- All three chronological ranks feed the same candidate's seven-field
word. Every other input is read from the original state below both passes. -/
theorem words (m : Memory w) (previous : D.Previous w) (room : D.endAddress<2^w)
    (pos : 0<D.lanes) (rankFit : D.lanes*max (D.bits*5) D.bits≤w/2)
    (maskFit : D.lanes*max (D.bits*9) (D.bits*7)≤w/2)
    (rankValues : ℕ→Fin D.hosts→Fin D.groups→Fin 5→Cell D.bits)
    (raw : ℕ→Fin D.hosts→Fin D.groups→Fin 9→Cell D.bits)
    (rankSource : ∀k<3*D.jobs,∀i,Source (D.rankReads k i) (fun v g=>rankValues k v g i) D.lanes m)
    (rawSource : ∀j<D.jobs,∀i : Fin 9, ¬(4≤ i.val ∧ i.val≤6) →
      Source (D.rawReads j i) (fun v g=>raw j v g i) D.lanes m)
    (classes : ∀j<D.jobs,∀(c : Fin 3) v g,
      raw j v g ⟨4+c.val,by omega⟩=D.rankOp (rankValues (3*j+c.val) v g)) :
    ∀j<D.jobs,Source (.lookup (D.output j) .row) (fun v g=>DescentCandidateMaskRAM.render (raw j v g))
      D.lanes (D.image m) := by
  let rank:=D.rankOp
  let mid:=D.ranks.image rank D.rankReads m
  have roomR : D.ranks.endAddress 5 D.bits<2^w:=D.ordered.2.trans_lt room
  have computed:=D.ranks.words rank D.rankReads m previous.rank roomR pos rankFit rankValues rankSource
  have prior:=D.ranks.any rank D.rankReads m previous.rank roomR
  apply D.masks.words DescentCandidateMaskRAM.render D.fields mid (D.fieldFits previous room) room pos maskFit raw
  intro j hj i
  change j < D.jobs at hj
  by_cases inside : 4≤ i.val ∧ i.val≤6
  · let c : Fin 3:=⟨i.val-4,by omega⟩
    have k : 3*j+c.val<3*D.jobs:=by have hc:=c.isLt; omega
    have same : (⟨4+c.val,by omega⟩ : Fin 9)=i:=Fin.ext (by dsimp [c];omega)
    have vals : (fun (v : Fin D.hosts) (g : Fin D.groups) => raw j v g i) =
        (fun v g => rank (rankValues (3*j+c.val) v g)) := by
      funext v g
      simpa only [same] using classes j hj c v g
    simp only [fields,dite_eq_left inside]
    change Source (.lookup (D.rankBank j c) .row)
      (fun (v : Fin D.hosts) (g : Fin D.groups) => raw j v g i) D.lanes mid
    rw [vals]
    exact computed (3*j+c.val) k
  · simp only [fields,dite_eq_right inside]
    intro row
    exact (eval_below _ _ m _ (previous.raw j hj i) (fun a ha=>prior.2.2 a (.inl ha))).trans (rawSource j hj i inside row)

theorem priced (rankLimit maskLimit : ℕ)
    (r : ∀j<3*D.jobs,(D.ranks.op D.rankOp D.rankReads j).work≤rankLimit)
    (s : ∀j<D.jobs,(D.masks.op (DescentCandidateMaskRAM.render (field:=D.bits)) D.fields j).work≤ maskLimit) :
    D.ticks≤D.ranks.costBound 5 D.bits rankLimit+D.masks.costBound 9 D.bits maskLimit ∧
    DescentStaticWordColumn.names (D.code w)≤
      D.ranks.nameBound 5 D.bits rankLimit+D.masks.nameBound 9 D.bits maskLimit := by
  obtain ⟨r₁,r₂⟩:=D.ranks.priced (w:=w) _ _ rankLimit r
  obtain ⟨s₁,s₂⟩:=D.masks.priced (w:=w) _ _ maskLimit s
  exact ⟨Nat.add_le_add r₁ s₁,(DescentStaticWordColumn.names_seq ..).le.trans (Nat.add_le_add r₂ s₂)⟩

end Mixed
end
end Hierarchy.DescentResetCandidateDate

end OAI
