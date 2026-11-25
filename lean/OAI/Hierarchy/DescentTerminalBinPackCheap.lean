import OAI.Hierarchy.DescentTerminalBinPack
import OAI.Hierarchy.ProtocolRAMSumScores
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Linear cheap-opcode prefix allocation of the physical terminal bins -/

namespace Hierarchy.DescentTerminalBinPackCheap
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM DescentTerminalBinPack
open scoped BigOperators Fin.CommRing

def nextBoundary (W u : ℕ) := u+(W-u%W)
def boundaries (bits W cap : ℕ) : Vector (Word bits) (cap+1) :=
  Vector.ofFn fun i=>((nextBoundary W i.val : ℕ):Word bits)

/-- The immutable next-boundary tape has one word per paid ordinal, plus
the exclusive end. The actual machine only does sequential reads, indirect
reads, comparisons and additions/subtractions. -/
def sizeTerm (bits counts out : ℕ) : SumScores.T bits :=
  .load (.binary .add (.literal counts) (.binary .sub (.result 0) (.literal out)))

def cutTerm (bits table out : ℕ) : SumScores.T bits :=
  .load (.binary .add (.literal table) (SumScores.prior bits out))

def step (bits counts table out : ℕ) : SumScores.T bits :=
  let size := sizeTerm bits counts out
  let cut := cutTerm bits table out
  let endAt := Term.binary .add (SumScores.prior bits out) size
  .select .lt cut endAt (.binary .add cut size) endAt

def program (bits counts table out sites : ℕ) :=
  PhysicalInputPhases.writing (step bits counts table out) Fin.elim0 out sites

theorem cost (bits counts table out : ℕ) : (step bits counts table out).binds=49 := by
  have binary (op : BinaryOp) (a b : SumScores.T bits) :
      (Term.binary op a b).binds = a.binds+b.binds+1 := by
    simp only [Term.binary,Term.binds_letThen,Term.binds_rename,Term.binds]; omega
  have select (op : Comparison) (a b c d : SumScores.T bits) :
      (Term.select op a b c d).binds = a.binds+b.binds+c.binds+d.binds+1 := by
    simp only [Term.select,Term.binds_letThen,Term.binds_rename,Term.binds]; omega
  have load (a : SumScores.T bits) : (Term.load a).binds = a.binds+1 := by
    simp only [Term.load,Term.binds_letThen,Term.binds]
  simp only [step,sizeTerm,cutTerm,SumScores.prior,select,binary,load,Term.literal,Term.binds]

theorem cheap (bits counts table out sites : ℕ) :
    CheapCode (program bits counts table out sites) := by
  apply writing_cheap
  simp [step,sizeTerm,cutTerm,SumScores.prior,Term.select,Term.binary,Term.load,Term.literal,
    admissible_let,admissible_rename,admissible,opAllowed,allowed]

private theorem cut_step {W : ℕ} (pos : 0<W) (u d : ℕ) :
    (if nextBoundary W u<u+d then nextBoundary W u+d else u+d)=startAt W u d+d := by
  have mod := Nat.mod_lt u pos
  unfold nextBoundary startAt
  split_ifs <;> omega

def Inputs {bits S : ℕ} (W src table cap : ℕ) (count : Fin S→ℕ) (m : Memory bits) :=
  (∀ i : Fin S,m (src+i.val)=(count i:Word bits)) ∧
  ∀ u : Fin (cap+1),m (table+u.val)=(boundaries bits W cap)[u.val]

def file {bits S : ℕ} (W out : ℕ) (count : Fin S→ℕ) (a : ℕ) : Word bits :=
  (cursor W count (a-out+1):Word bits)

theorem spec {bits S W : ℕ} (positive : 0<W) (src table out cap : ℕ) (count : Fin S→ℕ)
    (each : ∀i,count i ≤ W) (pool : purchased W count ≤ cap)
    (countsEnd : src+S ≤ out) (tableEnd : table+(cap+1) ≤ out)
    (outEnd : out+S<2^bits) (integerRoom : cap+W<2^bits) :
    (program bits src table out S).Spec (Inputs W src table cap count)
      (fun m dst=>dst=fillSegment out S (file W out count) m) (4+102*S) := by
  have bill : 4+102*S=4+S*(2*(step bits src table out).binds+4) := by rw [cost];omega
  rw [bill]
  apply SumScores.writing_prefix _ _ _ outEnd
  intro m hm a lo hi
  let k := a.val-out
  let i : Fin S := ⟨k,by dsimp [k];omega⟩
  let used := cursor W count k
  let size := count i
  let cut := nextBoundary W used
  let mem := fillSegment out k (file (bits:=bits) W out count) m
  have eqA : out+k=a.val := Nat.add_sub_of_le lo
  have kval : k<S := i.isLt
  have aeq : ((out+k:ℕ):Word bits)=a := by rw [eqA];exact Fin.cast_val_eq_self _
  have prev : (SumScores.prior bits out).eval Fin.elim0 mem (fun _=>a)=(used:Word bits) := by
    simp only [SumScores.prior,Term.eval_select,Term.eval_literal,Term.eval_load,Term.eval_binary,
      BinaryOp.eval,Comparison.test,beq_iff_eq]
    change (if a=(out:Word bits) then 0 else mem (a-1).val)=_
    have start : a=(out:Word bits) ↔ k=0 := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt (show out<2^bits by omega)]
      omega
    cases hk : k with
    | zero => simp [start.mpr hk,used,hk,cursor]
    | succ j =>
      have different : a≠(out:Word bits) := by intro h;have := start.mp h;omega
      have before : a-1=((out+j:ℕ):Word bits) := by rw [←aeq,hk,Nat.add_succ,Nat.cast_succ];abel
      have prevVal : (a-1).val=out+j :=
        (congrArg Fin.val before).trans (Fin.val_cast_of_lt (by omega))
      have written : out≤out+j ∧ out+j<out+k := by omega
      rw [ite_eq_right different,prevVal]
      change fillSegment out k (file W out count) m (out+j)=(used:Word bits)
      rw [fillSegment,ite_eq_left written]
      simp only [file,Nat.add_sub_cancel_left,used,hk]
  have sz : (sizeTerm bits src out).eval Fin.elim0 mem (fun _=>a)=(size:Word bits) := by
    have diff : a-(out:Word bits)=(k:Word bits) := by rw [←aeq,Nat.cast_add];abel
    simp only [sizeTerm,Term.eval_load,Term.eval_binary,Term.eval_literal,Term.eval,BinaryOp.eval,diff,
      ←Nat.cast_add,Fin.val_cast_of_lt (show src+k<2^bits by omega)]
    have untouched : ¬(out ≤ src+k ∧ src+k<out+k) := by omega
    simpa only [mem,fillSegment,ite_eq_right untouched,size,i] using hm.1 i
  have usedLe : used ≤ cap :=
    ((cursor_mono W count (show k ≤ S by omega)).trans (end_le_purchased positive count)).trans pool
  have edge : (cutTerm bits table out).eval Fin.elim0 mem (fun _=>a)=(cut:Word bits) := by
    simp only [cutTerm,Term.eval_load,Term.eval_binary,Term.eval_literal,BinaryOp.eval,prev,
      ←Nat.cast_add,Fin.val_cast_of_lt (show table+used<2^bits by omega)]
    let u : Fin (cap+1) := ⟨used,by omega⟩
    have untouched : ¬(out ≤ table+used ∧ table+used<out+k) := by omega
    simp only [mem,fillSegment,ite_eq_right untouched]
    simpa [u,boundaries,cut] using hm.2 u
  have bound : used+size<2^bits := (Nat.add_le_add usedLe (each i)).trans_lt integerRoom
  have edgeLt : cut<2^bits := (Nat.add_le_add usedLe (Nat.sub_le ..)).trans_lt integerRoom
  have test : ((cut:Word bits)<((used+size:ℕ):Word bits)) ↔ cut<used+size := by
    rw [Fin.lt_def,Fin.val_cast_of_lt edgeLt,Fin.val_cast_of_lt bound]
  change (step bits src table out).eval Fin.elim0 mem (fun _=>a)=_
  simp only [step,Term.eval_select,Term.eval_binary,BinaryOp.eval,Comparison.test,decide_eq_true_eq,prev,sz,edge,←Nat.cast_add,test]
  change (if cut<used+size then ((cut+size:ℕ):Word bits) else ((used+size:ℕ):Word bits))=
    (cursor W count (k+1):Word bits)
  rw [←apply_ite (fun n : ℕ=>(n:Word bits)),cut_step positive,cursor_step W count i]
  rfl

theorem read_interval {bits S W out : ℕ} (count : Fin S→ℕ) (m : Memory bits) (i : Fin S)
    (positive : 0<W) (fits : purchased W count<2^bits) :
    let e := (fillSegment out S (file (bits:=bits) W out count) m (out+i.val)).val
    e-count i=first W count i ∧ e-1=last W count i := by
  have lim := ((cursor_mono W count (show i.val+1 ≤ S from i.isLt)).trans (end_le_purchased positive count)).trans_lt fits
  have written : out≤out+i.val ∧ out+i.val<out+S := by have := i.isLt; omega
  simp only [fillSegment,ite_eq_left written,file,Nat.add_sub_cancel_left,Fin.val_cast_of_lt lim]
  rw [cursor_step W count i]
  exact ⟨Nat.add_sub_cancel ..,rfl⟩

theorem paid {S W : ℕ} (count : Fin S→ℕ) :
    purchased W count+1+(4+102*S) ≤ 2*(∑i,count i)+W+5+102*S := by
  have h := DescentTerminalBinPack.paid W count;omega

section Headers
variable {bits S W : ℕ}

def firstExpr (ends sizes : Bank) : Expr := .op .sub (.lookup ends .row) (.lookup sizes .row)
def lastExpr (ends : Bank) : Expr := .op .sub (.lookup ends .row) (.lit 1)

def headerProgram (bits S firstBase lastBase : ℕ) (ends sizes : Bank) :=
  (scan bits firstBase S (firstExpr ends sizes)).seq (scan bits lastBase S (lastExpr ends))

def headerImage (firstBase lastBase : ℕ) (ends sizes : Bank) (m : Memory bits) (n : ℕ) :=
  image lastBase n (lastExpr ends) (image firstBase n (firstExpr ends sizes) m)

private theorem image_at (out : ℕ) (e : Expr) (m : Memory bits) (i : Fin S) :
    image out S e m (out+i.val)=e.eval m (i.val:Word bits) := by
  simp [image,fillSegment,Nat.cast_add,show out+i.val<out+S by omega]

private theorem image_before (out S : ℕ) (e : Expr) (m : Memory bits) (j : ℕ) (before : j<out) :
    image out S e m j=m j := by simp [image,fillSegment,not_le.mpr before]

private theorem scan_pair (f l : ℕ) (x y : Expr) (m : Memory bits) (xf : x.Fits bits f)
    (yf : y.Fits bits l) (fr : f+S<2^bits) (lr : l+S<2^bits) :
    ((scan bits f S x).seq (scan bits l S y)).Exec m (image l S y (image f S x m))
        ((4+S*(2*x.work+4))+(4+S*(2*y.work+4))) ∧
      CheapCode ((scan bits f S x).seq (scan bits l S y)) := by
  constructor
  · exact Procedure.Exec.then (A:=scan bits f S x) (B:=scan bits l S y)
      (scan_exec f S x m xf fr) (scan_exec l S y _ yf lr)
  · apply cheap_seq (A:=scan bits f S x) (B:=scan bits l S y)
    · exact @scan_cheap bits f S x
    · exact @scan_cheap bits l S y

/-- Emit both endpoints as separate physical columns. The second pass
reads the exclusive-end bank below the first output, so it needs no copy. -/
theorem header_spec (f l : ℕ) (ends sizes : Bank) (m : Memory bits)
    (ef : ends.Fits bits f) (sf : sizes.Fits bits f) (separate : f+S ≤ l)
    (room : l+S<2^bits) :
    (headerProgram bits S f l ends sizes).Exec m (headerImage f l ends sizes m S)
      ((4+34*S)+(4+22*S)) ∧ CheapCode (headerProgram bits S f l ends sizes) := by
  have firstFit : (firstExpr ends sizes).Fits bits f := ⟨⟨ef,trivial⟩,sf,trivial⟩
  have lastFit : (lastExpr ends).Fits bits l := ⟨⟨⟨ef.1,ef.2.1,by have := ef.2.2;omega⟩,trivial⟩,trivial⟩
  have left : 34*S=S*(2*(firstExpr ends sizes).work+4) := by
    rw [show (firstExpr ends sizes).work=15 by rfl]
    omega
  have right : 22*S=S*(2*(lastExpr ends).work+4) := by
    rw [show (lastExpr ends).work=9 by rfl]
    omega
  rw [left,right]
  exact scan_pair f l (firstExpr ends sizes) (lastExpr ends) m firstFit lastFit (by omega) room

theorem header_read (f l : ℕ) (ends sizes : Bank) (count : Fin S→ℕ) (m : Memory bits)
    (i : Fin S) (live : 0<count i) (ef : ends.Fits bits f) (sf : sizes.Fits bits f)
    (enough : S ≤ ends.size) (charges : S ≤ sizes.size) (sep : f+S ≤ l)
    (endWord : m (ends.base+i.val)=((first W count i+count i:ℕ):Word bits))
    (sizeWord : m (sizes.base+i.val)=(count i:Word bits)) :
    headerImage f l ends sizes m S (f+i.val)=(first W count i:Word bits) ∧
    headerImage f l ends sizes m S (l+i.val)=(last W count i:Word bits) := by
  have bank (b : Bank) (fit : b.Fits bits f) (le : S ≤ b.size) (mem : Memory bits) :
      b.read mem (i.val:Word bits)=mem (b.base+i.val) := by
    have valid := i.isLt.trans_le le
    simp [Bank.read,Fin.val_cast_of_lt (valid.trans fit.2.1),Nat.mod_eq_of_lt valid]
  have old : ends.base+i.val<f := by have hi := i.isLt;have he := ef.2.2;omega
  unfold headerImage
  rw [image_before _ _ _ _ _ (by have hi:=i.isLt;omega),image_at,image_at]
  simp only [firstExpr,lastExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,
    bank ends ef enough,bank sizes sf charges,image_before _ _ _ _ _ old,endWord,sizeWord,
    Nat.cast_add,add_sub_cancel_right]
  simp [last,Nat.cast_sub (R:=Word bits) (show 1 ≤ first W count i+count i by omega)]

end Headers

end Hierarchy.DescentTerminalBinPackCheap

end OAI
