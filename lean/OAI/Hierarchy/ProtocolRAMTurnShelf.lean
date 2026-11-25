import OAI.Hierarchy.ProtocolRAMTurnDirectory
import OAI.Hierarchy.ProtocolRAMTurnReplay

namespace OAI
/-! # Compiling the chronological turn records into the paid site shelves -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnShelf
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAM
open scoped Fin.CommRing Classical

variable {W N sites slots : ℕ}

structure Tables where
  owner : Bank
  fieldBase : Bank
  dataOffset : Bank
  siteBase : Bank
  fields : Bank
  width : Bank
  site : Bank
  seat : Bank

def tables (rom romBits src srcBits N : ℕ) : Tables :=
  ⟨ProtocolRAMTurnDirectory.bank rom romBits 0,ProtocolRAMTurnDirectory.bank rom romBits 1,
   ProtocolRAMTurnDirectory.bank rom romBits 2,ProtocolRAMTurnDirectory.bank rom romBits 3,
   ⟨src,srcBits⟩,⟨src+4*N,srcBits⟩,⟨src+5*N,srcBits⟩,⟨src+6*N,srcBits⟩⟩

def addressExpr (A : Tables) (sink : ℕ) : Expr :=
  let i := Expr.lookup A.owner .row
  .branch .eq (.lookup A.width i) (.lit 0) (.lit sink)
    (.op .add (.op .add (.lookup A.fieldBase .row) (.lookup A.siteBase (.lookup A.site i)))
      (.lookup A.seat i))

def valueExpr (A : Tables) : Expr := .lookup A.fields (.lookup A.dataOffset .row)

def program (W N sites slots base scratch sink : ℕ) (A : Tables) : Procedure W :=
  ProtocolRAMTurnReplay.program W base (5*(sites*slots)) scratch (N*5) (addressExpr A sink) (valueExpr A)

theorem address_work (A : Tables) (sink : ℕ) : (addressExpr A sink).work=53 := rfl
theorem value_work (A : Tables) : (valueExpr A).work=12 := rfl

theorem work (N sites slots sink : ℕ) (A : Tables) :
    ProtocolRAMTurnReplay.work (5*(sites*slots)) (N*5) (addressExpr A sink) (valueExpr A)=
      15+30*(sites*slots)+740*N := by
  simp only [ProtocolRAMTurnReplay.work,ProtocolRAMGeneratedWrite.work,address_work,value_work]
  ring

theorem size (W N sites slots base scratch sink : ℕ) (A : Tables) :
    let p := program W N sites slots base scratch sink A
    p.labels=231 ∧ p.registers=83 ∧ p.slots=3 := by
  obtain ⟨cl,cr,cs⟩ := scan_size W base (5*(sites*slots)) (.lit 0)
  obtain ⟨al,ar,ast⟩ := scan_size W scratch (N*5) (addressExpr A sink)
  obtain ⟨vl,vr,vs⟩ := scan_size W (scratch+N*5) (N*5) (valueExpr A)
  change _+(_+_+12)=231 ∧ _+(_+_+5)=83 ∧ _+(_+_+3)=3
  simp [cl,cr,cs,al,ar,ast,vl,vr,vs,address_work,value_work,Expr.work]

private theorem indexedCheap (W a v n : ℕ) : CheapCode (ProtocolRAMIndexedWrite.scatter W a v n) := by
  intro P R K pc reg pub exit i
  change Fin 12 at i
  fin_cases i <;> trivial

private theorem sparseCheap (W base length scratch n : ℕ) (A V : Expr) :
    CheapCode (ProtocolRAMTurnReplay.program W base length scratch n A V) :=
  @cheap_seq W (scan W base length (.lit 0)) (ProtocolRAMGeneratedWrite.program W scratch (scratch+n) n A V)
    (scan_cheap W base length (.lit 0))
    (@cheap_seq W ((scan W scratch n A).seq (scan W (scratch+n) n V))
      (ProtocolRAMIndexedWrite.scatter W scratch (scratch+n) n)
      (@cheap_seq W (scan W scratch n A) (scan W (scratch+n) n V)
        (scan_cheap W scratch n A) (scan_cheap W (scratch+n) n V))
      (indexedCheap W scratch (scratch+n) n))

theorem cheap (W N sites slots base scratch sink : ℕ) (A : Tables) :
    CheapCode (program W N sites slots base scratch sink A) :=
  @sparseCheap W base (5*(sites*slots)) scratch (N*5) (addressExpr A sink) (valueExpr A)

/-- The seven columns are produced by the chronological itinerary scan. The first five are
left/right roles and starts followed by width. The last two are the paid site and local seat. -/
def Source (mem : Memory W) (src : ℕ) (col : Fin N → Fin 7 → ℕ) :=
  ∀ (i : Fin N) (f : Fin 7),f=4 ∨ col i 4≠0 → mem (src+f.val*N+i.val)=(col i f:Word W)

abbrev Live (col : Fin N→Fin 7→ℕ) := {i : Fin N // col i 4 ≠ 0}
abbrev Seats (sites slots : ℕ) := Fin sites × Fin slots

/-- A chronological visit names one semantic turn. Each site's independent paid
embedding (in particular WordSeats.allSeat) then gives the required global pair. -/
def paid {T V : Type*} {col : Fin N→Fin 7→ℕ} (visit : Live col ↪ T) (site : T→V)
    (code : V ↪ Fin sites) (seat : ∀v,{t : T // site t=v} ↪ Fin slots) :
    Live col ↪ Seats sites slots where
  toFun i := (code (site (visit i)),seat (site (visit i)) ⟨visit i,rfl⟩)
  inj' := by
    intro i j h
    have hv : site (visit i)=site (visit j) := code.injective (congrArg Prod.fst h)
    have transport (t : T) (v : V) (e : site t=v) :
        seat (site t) ⟨t,rfl⟩=seat v ⟨t,e⟩ := by cases e; rfl
    have move := transport (visit i) (site (visit j)) hv
    have same := (seat (site (visit j))).injective (move.symm.trans (congrArg Prod.snd h))
    exact visit.injective (congrArg Subtype.val same)

def entry (col : Fin N→Fin 7→ℕ) (put : Live col ↪ Seats sites slots)
    (f : Fin 5) : Seats sites slots → Word W :=
  Function.extend put (fun u => (col u.val (f.castLE (by decide)):Word W)) (fun _=>0)

@[simp] theorem entry_live (col : Fin N→Fin 7→ℕ) (put : Live col ↪ Seats sites slots)
    (f : Fin 5) (u : Live col) :
    entry (W:=W) col put f (put u)=(col u.val (f.castLE (by decide)):Word W) :=
  put.injective.extend_apply ..

theorem entry_blank (col : Fin N→Fin 7→ℕ) (put : Live col ↪ Seats sites slots)
    (f : Fin 5) (p : Seats sites slots) (unused : p ∉ Set.range put) :
    entry (W:=W) col put f p=0 :=
  Function.extend_apply' _ _ _ unused

def index (f : Fin 5) (p : Seats sites slots) : Fin (5*(sites*slots)) :=
  finProdFinEquiv (f,finProdFinEquiv p)

theorem index_val (f : Fin 5) (p : Seats sites slots) :
    (index f p).val=f.val*(sites*slots)+p.1.val*slots+p.2.val := by
  simp [index,finProdFinEquiv,Nat.add_comm,Nat.add_assoc,Nat.mul_comm]

private def pin (y : Fin (5*(sites*slots))) : Fin 5 × Seats sites slots :=
  let t : Fin 5 × Fin (sites*slots) := finProdFinEquiv.symm y
  (t.1,finProdFinEquiv.symm t.2)

@[simp] private theorem pin_index (f : Fin 5) (p : Seats sites slots) : pin (index f p)=(f,p) := by
  simp [pin,index]

@[simp] private theorem index_pin (y : Fin (5*(sites*slots))) :
    index (pin y).1 (pin y).2=y := by
  obtain ⟨⟨f,q⟩,rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨p,rfl⟩ := finProdFinEquiv.surjective q
  exact congrArg (fun q => index q.1 q.2) (pin_index f p)

private def dest (base sink : ℕ) (col : Fin N→Fin 7→ℕ) (put : Live col ↪ Seats sites slots)
    (t : Fin (N*5)) : ℕ :=
  let p : Fin N × Fin 5 := finProdFinEquiv.symm t
  if h : col p.1 4=0 then sink else base+(index p.2 (put ⟨p.1,h⟩)).val


theorem run (rom rb src sb base scratch sink : ℕ) (mem : Memory W) (col : Fin N→Fin 7→ℕ)
    (put : Live col ↪ Seats sites slots)
    (loc : ∀ u : Live col, (put u).1.val=col u.val 5 ∧ (put u).2.val=col u.val 6)
    (input : Source mem src col)
    (directory : ∀ (j : Fin 4) (t : ℕ),t<2^rb →
       (ProtocolRAMTurnDirectory.bank rom rb j).read mem (t:Word W)=
         ProtocolRAMTurnDirectory.words N sites slots base j t)
    (romRows : N*5≤2^rb) (romSites : sites≤2^rb) (fieldRoom : 5*N≤2^sb)
    (sourceWord : 2^sb≤2^W) (validWidth : ∀ i,col i 4<2^W)
    (before : base+5*(sites*slots)≤ scratch) (fit : scratch+(N*5)+(N*5)<2^W)
    (sinkLow : sink<base) (af : (addressExpr (tables rom rb src sb N) sink).Fits W base)
    (vf : (valueExpr (tables rom rb src sb N)).Fits W base) :
    let A := tables rom rb src sb N
    ∃ out,(program W N sites slots base scratch sink A).Exec mem out
        (ProtocolRAMTurnReplay.work (5*(sites*slots)) (N*5) (addressExpr A sink) (valueExpr A)) ∧
      (∀ (f : Fin 5) (p : Seats sites slots),out (base+f.val*(sites*slots)+p.1.val*slots+p.2.val)=entry col put f p) ∧
      ∀ t,(t<base ∨ base+5*(sites*slots)≤t) →
        (t<scratch ∨ scratch+(N*5)+(N*5)≤t) → t≠sink → out t=mem t := by
  intro A
  let raw (j : Fin (5*(sites*slots))) : Word W := entry col put (pin j).1 (pin j).2
  have rowsFit (i : Fin N) : i.val<2^sb := by have := i.isLt;omega
  have read (f : Fin 7) (i : Fin N) (use : f=4 ∨ col i 4≠0) :
      (⟨src+f.val*N,sb⟩ : Bank).read mem (i.val:Word W)=(col i f:Word W) := by
    change mem (src+f.val*N+(i.val:Word W).val%2^sb)=_
    rw [Fin.val_cast_of_lt ((rowsFit i).trans_le sourceWord),Nat.mod_eq_of_lt (rowsFit i)]
    exact input i f use
  have select (i : Fin N) (f : Fin 5) (j : Fin 3) :
      (ProtocolRAMTurnDirectory.bank rom rb (j.castLE (by decide))).read mem
        ((finProdFinEquiv (i,f)).val:Word W)=
          (ProtocolRAMTurnDirectory.fieldWords N sites slots base i f j:Word W) :=
    (directory _ _ ((finProdFinEquiv (i,f)).isLt.trans_le romRows)).trans
      (ProtocolRAMTurnDirectory.packed N sites slots base i f j)
  have ha (t : Fin (N*5)) : (addressExpr A sink).eval mem (t.val:Word W)=(dest base sink col put t:Word W) := by
    obtain ⟨⟨i,f⟩,rfl⟩ := finProdFinEquiv.surjective t
    let t : Fin (N*5) := finProdFinEquiv (i,f)
    have owner : A.owner.read mem (t.val:Word W)=(i.val:Word W) := select i f 0
    have off : A.fieldBase.read mem (t.val:Word W)=((base+f.val*(sites*slots):ℕ):Word W) := select i f 1
    have width : A.width.read mem (i.val:Word W)=(col i 4:Word W) := read 4 i (.inl rfl)
    have zero : (col i 4:Word W)=0 ↔ col i 4=0 := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt (validWidth i)];rfl
    change (addressExpr A sink).eval mem (t.val:Word W)=_
    simp only [addressExpr,Expr.eval,Comparison.test,beq_iff_eq,RowOp.opcode,BinaryOp.eval,
      Nat.cast_zero,owner,off,width,zero,dest,Equiv.symm_apply_apply]
    by_cases h : col i 4=0
    · simp [h]
    · have site : A.site.read mem (i.val:Word W)=(col i 5:Word W) := read 5 i (.inr h)
      have seat : A.seat.read mem (i.val:Word W)=(col i 6:Word W) := read 6 i (.inr h)
      have hs := (loc ⟨i,h⟩).1
      have hl := (loc ⟨i,h⟩).2
      have sb := ((put ⟨i,h⟩).1.isLt.trans_le romSites)
      have orig : A.siteBase.read mem (col i 5:Word W)=((col i 5*slots:ℕ):Word W) :=
        (directory 3 (col i 5) (hs ▸ sb)).trans (ProtocolRAMTurnDirectory.site N sites slots base _)
      have notDiv : ¬ 2^W ∣ col i 4 :=
        fun hd => (Nat.not_le_of_lt (validWidth i)) (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd)
      simp [h,site,seat,orig,index_val,hs,hl,Nat.cast_add,add_assoc]
  let actual (t : Fin (N*5)) := (valueExpr A).eval mem (t.val:Word W)
  have hv (i : Fin N) (f : Fin 5) (live : col i 4≠0) :
      actual (finProdFinEquiv (i,f))=(col i (f.castLE (by decide)):Word W) := by
    have off : A.dataOffset.read mem ((finProdFinEquiv (i,f)).val:Word W)=((f.val*N+i.val:ℕ):Word W) :=
      select i f 2
    have cap : f.val*N+i.val<2^sb := by
      have h := Nat.mul_le_mul_right N f.isLt
      rw [Nat.succ_mul] at h
      have := i.isLt
      omega
    simp only [actual,valueExpr,Expr.eval,off]
    change mem (src+((f.val*N+i.val:ℕ):Word W).val%2^sb)=_
    rw [Fin.val_cast_of_lt (cap.trans_le sourceWord),Nat.mod_eq_of_lt cap,← Nat.add_assoc]
    exact input i (f.castLE (by decide)) (.inr live)
  have bound (t : Fin (N*5)) : dest base sink col put t=sink ∨
      (base≤dest base sink col put t ∧ dest base sink col put t<base+5*(sites*slots)) := by
    obtain ⟨⟨i,f⟩,rfl⟩ := finProdFinEquiv.surjective t
    simp only [dest,Equiv.symm_apply_apply]
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (Fin.isLt _) _⟩
  have agree (t : Fin (N*5)) (j : Fin (5*(sites*slots)))
      (same : dest base sink col put t=base+j.val) : actual t=(raw j : Word W) := by
    obtain ⟨⟨i,f⟩,rfl⟩ := finProdFinEquiv.surjective t
    simp only [dest,Equiv.symm_apply_apply] at same
    split at same
    · omega
    · rename_i h
      have hj : index f (put ⟨i,h⟩)=j := Fin.ext (Nat.add_left_cancel same)
      subst j
      rw [hv i f h]
      simp only [raw,pin_index,entry,put.injective.extend_apply]
  have cover (j : Fin (5*(sites*slots))) : raw j=0 ∨ ∃ t,dest base sink col put t=base+j.val := by
    by_cases h : (pin j).2∈Set.range put
    · obtain ⟨u,hu⟩ := h
      refine Or.inr ⟨finProdFinEquiv (u.val,(pin j).1),?_⟩
      simp [dest,u.property,hu]
    · exact Or.inl (Function.extend_apply' _ _ _ h)
  obtain ⟨out,exec,all,frame⟩ := ProtocolRAMTurnReplay.run base _ scratch sink _ _ mem _ actual raw
    af vf before fit (by omega) ha (fun _=>rfl) bound agree cover
  refine ⟨out,exec,?_,frame⟩
  intro f p
  simpa only [index_val,Nat.add_assoc,raw,pin_index] using all (index f p)

end Hierarchy.ProtocolRAMTurnShelf

end
end OAI
