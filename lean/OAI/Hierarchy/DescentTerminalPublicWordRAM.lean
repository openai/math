import OAI.Hierarchy.DescentTerminalPublicWords
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # One cheap gather per real whole-word exterior row, including shared homes -/

namespace Hierarchy.DescentTerminalPublicWordRAM
open DescentExterior DescentGL DescentTerminalPublicWords ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing BigOperators

structure Tapes where
  portAt : Bank
  lowAt : Bank
  slab : Bank
  high : Bank
  slabBase : Bank
  highBase : Bank
  phase : Bank

def row (L : Tapes) (rows : ℕ) : Expr :=
  let z:=Expr.lookup L.portAt .row
  let slab:=Expr.lookup L.slabBase (.lookup L.slab z)
  let group:=Expr.lookup L.highBase (.lookup L.high z)
  .branch .lt .row (.lit rows)
    (.lookup L.phase (.op .add (.op .add slab group) (.lookup L.lowAt .row))) (.lit 0)

def program (bits out rows : ℕ) (L : Tapes) := scan bits out (rows+2) (row L rows)

theorem work (L : Tapes) (rows : ℕ) : (row L rows).work=53 := rfl

variable {bits p span E A R : ℕ} {P : Type} [Fintype P]

/-- These two immutable columns list only the paid physical destination rows. -/
def portAt (bits p span : ℕ) := Vector.ofFn fun i : Fin (p*span)=>((finProdFinEquiv.symm i).1.val:Word bits)
def lowAt (bits p span : ℕ) := Vector.ofFn fun i : Fin (p*span)=>((finProdFinEquiv.symm i).2.val:Word bits)
def multiples (bits n stride : ℕ) := Vector.ofFn fun i : Fin n=>((i.val*stride:ℕ):Word bits)

def all (L : Tapes) := [L.portAt,L.lowAt,L.slab,L.high,L.slabBase,L.highBase,L.phase]
def Fits (L : Tapes) (bits out : ℕ) := ∀b∈all L,b.Fits bits out

def Controls (L : Tapes) (rank : P ≃ Fin (Fintype.card P)) (field : P→Fin E×Fin A)
    (span R : ℕ) (m : Memory bits) :=
  (∀i : Fin (Fintype.card P*span),L.portAt.read m (i.val:Word bits)=(portAt bits (Fintype.card P) span)[i.val]) ∧
  (∀i : Fin (Fintype.card P*span),L.lowAt.read m (i.val:Word bits)=(lowAt bits (Fintype.card P) span)[i.val]) ∧
  (∀z,L.slab.read m ((rank z).val:Word bits)=((field z).1.val:Word bits)) ∧
  (∀z,L.high.read m ((rank z).val:Word bits)=((field z).2.val:Word bits)) ∧
  (∀a : Fin E,L.slabBase.read m (a.val:Word bits)=(multiples bits E R)[a.val]) ∧
  (∀a : Fin A,L.highBase.read m (a.val:Word bits)=(multiples bits A span)[a.val])

def Inputs (L : Tapes) (rank : P ≃ Fin (Fintype.card P)) (field : P→Fin E×Fin A)
    (span R : ℕ) (data : Fin (E*R)→Word bits) (m : Memory bits) :=
  Controls L rank field span R m ∧ ∀i : Fin (E*R),L.phase.read m (i.val:Word bits)=data i

def request (rank : P ≃ Fin (Fintype.card P)) (field : P→Fin E×Fin A) (split : A*span=R)
    (i : Fin (Fintype.card P*span)) : Fin (E*R) :=
  let rows:=finProdFinEquiv.symm i
  let f:=field (rank.symm rows.1)
  finProdFinEquiv (f.1,(finProdFinEquiv (f.2,rows.2)).cast split)

theorem request_val (rank : P ≃ Fin (Fintype.card P)) (field : P→Fin E×Fin A) (split : A*span=R)
    (i : Fin (Fintype.card P*span)) :
    let rows:=finProdFinEquiv.symm i
    let f:=field (rank.symm rows.1)
    (request rank field split i).val=f.1.val*R+f.2.val*span+rows.2.val := by
  intro rows f
  change (rows.2.val+span*f.2.val)+R*f.1.val=_
  ring

theorem exec_image (L : Tapes) (out : ℕ) (rank : P ≃ Fin (Fintype.card P)) (field : P→Fin E×Fin A)
    (split : A*span=R) (data : Fin (E*R)→Word bits) (m : Memory bits) (fit : Fits L bits out)
    (room : out+(Fintype.card P*span+2)<2^bits) (src : Inputs L rank field span R data m) :
    let n:=Fintype.card P*span
    let after:=image out (n+2) (row L n) m
    (program bits out n L).Exec m after (4+(n+2)*(2*53+4)) ∧
      (∀i : Fin n,after (out+i.val)=data (request rank field split i)) ∧
      after (out+n)=0 ∧ after (out+(n+1))=0 := by
  intro n after
  obtain ⟨⟨pa,la,sl,hi,sb,hb⟩,col⟩:=src
  have efit : (row L n).Fits bits out := by
    simp only [row,Expr.Fits,fit L.portAt (by simp [all]),fit L.lowAt (by simp [all]),
      fit L.slab (by simp [all]),fit L.high (by simp [all]),fit L.slabBase (by simp [all]),
      fit L.highBase (by simp [all]),fit L.phase (by simp [all]),and_self]
  refine ⟨@scan_exec bits out (n+2) (row L n) m efit room,?_⟩
  have read (k : ℕ) (good : k<n+2) :
      after (out+k)=(row L n).eval m (k:Word bits) := by
    simp [after,ProtocolRAM.image,fillSegment,good,Nat.cast_add]
  have guard (k : ℕ) (ht : k<n+2) : ((k:Word bits)<(n:Word bits)) ↔ k<n := by
    rw [Fin.lt_def,Fin.val_cast_of_lt (by omega),Fin.val_cast_of_lt (by omega)]
  refine ⟨fun i=>?_,?_,?_⟩
  · rw [read i.val (by have:=i.isLt;omega)]
    let pair : Fin (Fintype.card P) × Fin span := finProdFinEquiv.symm i
    let f:=field (rank.symm pair.1)
    have port : L.portAt.read m (i.val:Word bits)=(pair.1.val:Word bits) := by
      simpa only [portAt,Vector.getElem_ofFn] using pa i
    have low : L.lowAt.read m (i.val:Word bits)=(pair.2.val:Word bits) := by
      simpa only [lowAt,Vector.getElem_ofFn] using la i
    simp only [row,Expr.eval,RowOp.opcode,BinaryOp.eval,DescriptorExpr.Comparison.test,decide_eq_true_eq,
      guard i.val (by have:=i.isLt;omega),ite_eq_left i.isLt,port,low]
    have s : L.slab.read m (pair.1.val:Word bits)=(f.1.val:Word bits) := by simpa [f] using sl (rank.symm pair.1)
    have h : L.high.read m (pair.1.val:Word bits)=(f.2.val:Word bits) := by simpa [f] using hi (rank.symm pair.1)
    rw [s,h,sb f.1,hb f.2]
    simp only [multiples,Vector.getElem_ofFn,←Nat.cast_add]
    have addr : (request rank field split i).val = f.1.val * R + f.2.val * span + pair.2.val :=
      request_val rank field split i
    rw [←addr,col]
  · rw [read n (by omega)]
    simp [row,Expr.eval,DescriptorExpr.Comparison.test]
  · rw [read (n+1) (by omega)]
    simp only [row,Expr.eval,DescriptorExpr.Comparison.test,decide_eq_true_eq,
      guard (n+1) (by omega),show ¬n+1<n by omega,ite_false,Nat.cast_zero]

theorem exec (L : Tapes) (out : ℕ) (rank : P ≃ Fin (Fintype.card P)) (field : P→Fin E×Fin A)
    (split : A*span=R) (data : Fin (E*R)→Word bits) (m : Memory bits) (fit : Fits L bits out)
    (room : out+(Fintype.card P*span+2)<2^bits) (src : Inputs L rank field span R data m) :
    let n:=Fintype.card P*span
    ∃after,(program bits out n L).Exec m after (4+(n+2)*(2*53+4)) ∧
      (∀i : Fin n,after (out+i.val)=data (request rank field split i)) ∧
      after (out+n)=0 ∧ after (out+(n+1))=0 := ⟨_,exec_image L out rank field split data m fit room src⟩

theorem cheap (bits out n : ℕ) (L : Tapes) : CheapCode (program bits out n L) := @scan_cheap _ _ _ _

/-- The slab and field-prefix tables depend solely on geometry. The two
enumeration tables and the fetched output are each linear in the real
paid whole-row count. No original-stack lookup occurs in this scan. -/
theorem charge {p span E A : ℕ} (nonempty : 0<span) :
    2*(p*span)+E+A+2*p+(4+(p*span+2)*(2*53+4)) ≤ E+A+224+114*(p*span) := by
  have le:=Nat.le_mul_of_pos_right p nonempty
  omega

theorem populated_charge {p span E A : ℕ} (nonempty : 0<span) (slabs : 0<E) (groups : 0<A) (full : p=E*A) :
    2*(p*span)+E+A+2*p+(4+(p*span+2)*(2*53+4)) ≤ 224+116*(p*span) := by
  have e: E ≤ p := full ▸ Nat.le_mul_of_pos_right _ groups
  have a : A ≤ p := by rw [full,Nat.mul_comm];exact Nat.le_mul_of_pos_right _ slabs
  have h:=Nat.le_mul_of_pos_right p nonempty
  have cost:=charge (p:=p) (E:=E) (A:=A) nonempty
  omega

section Actual
open DescentColonies DescentInitialHost DescentSixParty Computability.BorderVNP.Crossing CorrectionFrame DescentExteriorFetch
open ThreeFlat Routing Catalyst CatalystSubstitution CorrectionBatch
open DescentTerminalDenseWindow DescentTerminalDenseGraphRead
open scoped Classical
variable {F : Type} [Field F] {arity data j r t : ℕ} (X : Approximation F arity data)
    {width : P→ℕ}

omit [Field F] in
/-- Starting in the genuine phase-three memory, this single native pass
assembles every whole dense public source row in home order. Its two
additional words are zero, as required by a two-word dense gather. -/
theorem actual (L : Tapes) (out : ℕ) (rank : P ≃ Fin (Fintype.card P)) (field : P→Fin (ExteriorCount X)×Fin A)
    (split : A*span=(2^(j+r))) (widthEq : ∀z,width z=span*(2^j*t))
    (M : Fin (ExteriorCount X)→Layout (j+(j+r))) (x : Catalyst.Port ((2^(j+(j+r))*t)*data) (copiesWidth (2^(j+(j+r))*t) X.width)→Bool)
    (z : Hidden (ExteriorCount X) j r t→Bool) {keyAt start : ℕ} (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (ready : ∀s,(columns g guess s).Fits bits start) (m : Memory bits)
    (cap : ∀s,Capacity (g s) bits j r t (ExteriorCount X) start)
    (input : ∀s,DescentExteriorFetch.Inputs (g s) s M (passInputs (publicRows (j:=j) (r:=r) (t:=t) X x) z s) (ProtocolRAM.image keyAt ((ExteriorCount X)*(2^(j+r))) (joinKey kb) m))
    (phases : ∀a,stagesOK (M a) (publicRows (j:=j) (r:=r) (t:=t) X x a) (projected z false a) (projected z true a))
    (fit : Fits L bits out) (outRoom : out+(Fintype.card P*span+2)<2^bits)
    (phaseBase : L.phase.base=start+2*((ExteriorCount X)*(2^(j+r)))) (phaseRoom : (ExteriorCount X)*(2^(j+r)) ≤ L.phase.size)
    (ctrl : Controls L rank field span (2^(j+r)) (finalMem keyAt start ((ExteriorCount X)*(2^(j+r))) kb g guess m)) :
    let n:=Fintype.card P*span
    ∃after,(program bits out n L).Exec (finalMem keyAt start ((ExteriorCount X)*(2^(j+r))) kb g guess m) after (4+(n+2)*(2*53+4)) ∧
      (∀i : Fin n,after (out+i.val)=((dense (2^j*t) (publicStream (ord rank)
        (outer X field split widthEq M x)) i.val).val:Word bits)) ∧ after (out+n)=0 ∧ after (out+(n+1))=0 := by
  intro n
  let final:=finalMem keyAt start ((ExteriorCount X)*(2^(j+r))) kb g guess m
  let value:=fun i : Fin ((ExteriorCount X)*(2^(j+r)))=>final (start+2*((ExteriorCount X)*(2^(j+r)))+i.val)
  have col (i : Fin ((ExteriorCount X)*(2^(j+r)))) : L.phase.read final (i.val:Word bits)=value i := by
    have good:=i.isLt.trans_le phaseRoom
    have f:=fit L.phase (by simp [all])
    simp [Bank.read,Fin.val_cast_of_lt (good.trans f.2.1),Nat.mod_eq_of_lt good,value,phaseBase]
  obtain ⟨after,run,read,s0,s1⟩:=exec L out rank field split value final fit outRoom ⟨ctrl,col⟩
  refine ⟨after,run,?_,s0,s1⟩
  intro i
  obtain ⟨⟨u,s⟩,rfl⟩:=finProdFinEquiv.surjective i
  rw [read]
  have h:=native_word X field split widthEq rank M x z kb g guess ready m cap input phases (rank.symm u) s
  simpa only [value,request,Equiv.symm_apply_apply,Equiv.apply_symm_apply,DescentTerminalPublicWords.request,
    rowOffset,final] using h

end Actual

end Hierarchy.DescentTerminalPublicWordRAM

end OAI
