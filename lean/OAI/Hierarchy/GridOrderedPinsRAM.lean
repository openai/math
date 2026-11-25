import OAI.Hierarchy.GridThroughOrdered
import OAI.Hierarchy.GridWiringNetwork
import OAI.Hierarchy.GridApproximationAdvice
import OAI.Hierarchy.GridRailNumeric
import OAI.Hierarchy.GridTopologyRAM

namespace OAI
/-! # Native generation of the original-template port map

The compact advice numbers the original network's ports. Its three-word
decoding table distinguishes data ports from catalyst ends. Each original
copy reads the same decoding table. -/

namespace Hierarchy.GridOrderedPinsRAM
open GridThrough GridThrough.Ordered ThreeFlat UniversalGrid
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.BitLayout RAM.DescriptorExpr GridTopologyRAM
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {k p n r w : ℕ}
variable (X : Catalyst.Approximation F k p) (P : GridThrough.Program (Fin r) n p X.width)

structure Banks where
  compact : ℕ
  data : ℕ
  chosen : ℕ
  stride : ℕ
  output : ℕ

private abbrev T (w : ℕ) := Term w 9 2
private abbrev Q (w : ℕ) := Term w 9 1

def words (S : Banks) (B k p r _g : ℕ) : Fin 9 → Word w :=
  ![S.compact,S.data,S.chosen,S.stride,S.output,B,k,p,(2+r*2:ℕ)]

private abbrev add {v} (a b : Term w 9 v) : Term w 9 v := .binary .add a b
private abbrev mul {v} (a b : Term w 9 v) : Term w 9 v := .binary .mul a b
private abbrev val {v} (a : ℕ) : Term w 9 v := .literal (a:Word w)
private def load {v} (base off : Term w 9 v) : Term w 9 v := .load (add base off)
private def header {v} (i : ℕ) : Term w 9 v := load (.parameter 0) (val i)
private def descriptorBase : T w := add (add (.parameter 0) (add (val 6) (.parameter 6)))
  (mul (val 11) (header 3))
private def field (d : ℕ) : T w := load descriptorBase (add (mul (val 3) (.result 1)) (val d))
private def dataPtr : T w := load (.parameter 1) (add (mul (.result 0) (.parameter 7)) (field 2))
private def useRail : T w := load (.parameter 2)
  (add (mul (add (mul (.result 0) (.parameter 6)) (field 1)) (.parameter 5)) (field 2))
private def bitIndex : T w := .binary .div (.result 0) (load (.parameter 3) (field 1))

/-- Two logical register inputs: cell ordinal and original pin ordinal.
The grid side is known to the uniform generator at each public length. -/
def body (g : ℕ) : T w :=
  .select .eq (field 0) (val 0) dataPtr
    (add (.parameter 8)
      (add (mul (mul useRail (val g)) (val 2))
        (add (mul (val 2) (.binary .mod bitIndex (val g))) (.binary .sub (field 0) (val 1)))))

private def offset : Q w := .binary .sub (.result 0) (.parameter 4)
private def raw (g : ℕ) : Q w := (body g).instantiate
  ![.binary .div offset (header 4),.binary .mod offset (header 4)]

/-- The padded scan has a cap from the public length, and obtains the actual
pin count from the small advice header before decoding the two indices. -/
def program (L g : ℕ) : Q w :=
  .select .lt offset (mul (val L) (header 4)) (raw g) (val 0)

private def ptr (a : Addr r n) := sourceAddress (Wiring.source a)

structure Mounted (S : Banks) (B : ℕ) (m : Memory w) : Prop where
  cells : m (S.compact+3)=(X.network.cells:Word w)
  ports : m (S.compact+4)=(GridApproximationAdvice.portCount X:Word w)
  tags : ∀ (i : Fin (GridApproximationAdvice.portCount X)) (f : Fin 3),
    m (S.compact+GridApproximationAdvice.portBase X+(3*i.val+f.val)) =
      (GridApproximationAdvice.descriptor X ((Fintype.equivFin _).symm i) f:Word w)
  localData : ∀ c : Cell k n, ∀ i : Fin p,
    m (S.data+((finFunctionFinEquiv c).val*p+i.val)) =
      (ptr (sourcePin P P.data c (.inl i)):Word w)
  chosenRail : ∀ c : Cell k n, ∀ u : Catalyst.Wire X.width,
    m (S.chosen+(((finFunctionFinEquiv c).val*k+u.1.val)*B+u.2.val)) =
      ((P.pass c u).val:Word w)
  stride : ∀ j : Fin k,m (S.stride+j.val)=((n+1)^j.val:Word w)

theorem mounted_of_packed (S : Banks) (B : ℕ) (code : FieldCode F w) (m original : Memory w)
    (cap : GridApproximationAdvice.wordCount X ≤ 12*B)
    (keep : ∀ i < GridApproximationAdvice.wordCount X, m (S.compact+i)=
      GridApproximationAdvice.paddedMemory X code B S.compact original (S.compact+i))
    (localData : ∀ c : Cell k n, ∀ i : Fin p, m (S.data+((finFunctionFinEquiv c).val*p+i.val)) =
      (ptr (sourcePin P P.data c (.inl i)):Word w))
    (chosenRail : ∀ c : Cell k n, ∀ u : Catalyst.Wire X.width,
      m (S.chosen+(((finFunctionFinEquiv c).val*k+u.1.val)*B+u.2.val)) =
      ((P.pass c u).val:Word w))
    (stride : ∀ j : Fin k,m (S.stride+j.val)=((n+1)^j.val:Word w)) : Mounted X P S B m := by
  have read (i : ℕ) (hi : i < GridApproximationAdvice.wordCount X) :
      m (S.compact+i)=GridApproximationAdvice.packed X code S.compact original (S.compact+i) :=
    (keep i hi).trans (GridApproximationAdvice.paddedMemory_eq X code B S.compact original i hi cap)
  have head (j : Fin 6) : j.val < GridApproximationAdvice.wordCount X := by
    have := j.isLt
    unfold GridApproximationAdvice.wordCount GridApproximationAdvice.multBase
      GridApproximationAdvice.portBase GridApproximationAdvice.rowBase
    omega
  refine ⟨(read 3 (head 3)).trans (GridApproximationAdvice.packed_header X code _ original 3),
    (read 4 (head 4)).trans (GridApproximationAdvice.packed_header X code _ original 4),?_,
    localData,chosenRail,stride⟩
  intro i j
  rw [Nat.add_assoc,read]
  · exact GridApproximationAdvice.packed_port X code S.compact original i j
  · have := i.isLt
    have := j.isLt
    unfold GridApproximationAdvice.wordCount GridApproximationAdvice.multBase
    omega

structure Fits (S : Banks) (B : ℕ) : Prop where
  grid : n+1 < 2^w
  cells : (n+1)^k < 2^w
  widths : ∀ j, X.width j ≤ B
  ports : GridApproximationAdvice.portCount X ≤ B
  compact : S.compact+GridApproximationAdvice.multBase X < 2^w
  data : S.data+(n+1)^k*p ≤ 2^w
  chosen : S.chosen+((n+1)^k*k)*B ≤ 2^w
  stride : S.stride+k ≤ 2^w
  output : S.output+(n+1)^k*B < 2^w
  cap : B < 2^w

private theorem below {base pitch count : ℕ} (i : Fin count) (j : Fin pitch) :
    base+(i.val*pitch+j.val) < base+count*pitch := by
  have le := Nat.mul_le_mul_right pitch i.isLt
  rw [Nat.succ_mul] at le
  have := j.isLt
  omega

private theorem result_at {d : ℕ} (q : Fin d) (u : Fin 9 → Word w) (m : Memory w) (v : Fin d → Word w) :
    (Term.result q).eval u m v=v q := rfl

private theorem field_eval (d : ℕ) (u : Fin 9 → Word w) (m : Memory w) (v : Fin 2 → Word w) :
    (field d).eval u m v = m (((u 0+(6+u 6)+11*m (u 0+3).val)+(3*v 1+(d:Word w))).val) := by
  simp only [field,descriptorBase,header,load,Term.eval_load,Term.eval_binary,Term.eval_literal,
    Term.eval_parameter,result_at,BinaryOp.eval,Nat.cast_ofNat]

private theorem data_eval (u : Fin 9 → Word w) (m : Memory w) (v : Fin 2 → Word w) :
    dataPtr.eval u m v = m ((u 1+(v 0*u 7+(field 2).eval u m v)).val) := by
  simp only [dataPtr,load,Term.eval_load,Term.eval_binary,Term.eval_parameter,result_at,BinaryOp.eval]

private theorem rail_eval (u : Fin 9 → Word w) (m : Memory w) (v : Fin 2 → Word w) :
    useRail.eval u m v = m ((u 2+((v 0*u 6+(field 1).eval u m v)*u 5+(field 2).eval u m v)).val) := by
  simp only [useRail,load,Term.eval_load,Term.eval_binary,Term.eval_parameter,result_at,BinaryOp.eval]

private theorem bit_eval (u : Fin 9 → Word w) (m : Memory w) (v : Fin 2 → Word w) :
    bitIndex.eval u m v = BinaryOp.eval .div (v 0) (m ((u 3+(field 1).eval u m v).val)) := by
  simp only [bitIndex,load,Term.eval_binary,Term.eval_load,Term.eval_parameter,result_at,BinaryOp.eval]

private theorem body_eval (g : ℕ) (u : Fin 9 → Word w) (m : Memory w) (v : Fin 2 → Word w) :
    (body g).eval u m v = if (field 0).eval u m v=0 then dataPtr.eval u m v else
      u 8+(useRail.eval u m v*(g:Word w)*2+
        (2*(BinaryOp.eval .mod (bitIndex.eval u m v) (g:Word w))+((field 0).eval u m v-1))) := by
  simp only [body,Term.eval_select,Term.eval_binary,Term.eval_parameter,Term.eval_literal,
    Comparison.test,beq_iff_eq,BinaryOp.eval,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]

omit [Field F] [Fintype F] in
private theorem load_field (S : Banks) (B : ℕ) (m : Memory w) (mounted : Mounted X P S B m)
    (fit : Fits (n:=n) (w:=w) X S B) (c : Cell k n)
    (i : Fin (GridApproximationAdvice.portCount X)) (d : Fin 3) :
    (field d.val).eval (words S B k p r (n+1)) m
      ![((finFunctionFinEquiv c).val:Word w),(i.val:Word w)] =
      (GridApproximationAdvice.descriptor X ((Fintype.equivFin _).symm i) d:Word w) := by
  have head : S.compact+3 < 2^w := by
    have := fit.compact
    unfold GridApproximationAdvice.multBase GridApproximationAdvice.portBase GridApproximationAdvice.rowBase at this
    omega
  have addr : S.compact+GridApproximationAdvice.portBase X+(3*i.val+d.val) < 2^w := by
    have bound := below (base:=S.compact+GridApproximationAdvice.portBase X) i d
    have := fit.compact
    unfold GridApproximationAdvice.multBase at this
    nlinarith
  rw [field_eval]
  change m (((((S.compact:Word w)+(6+(k:Word w))) +
      11*m (((S.compact:Word w)+3).val)) + (3*(i.val:Word w)+(d.val:Word w))).val)=_
  rw [show (S.compact:Word w)+3=((S.compact+3:ℕ):Word w) by simp,
    Fin.val_cast_of_lt head,mounted.cells]
  have eq : ((S.compact:Word w)+(6+(k:Word w))+11*(X.network.cells:Word w))+
      (3*(i.val:Word w)+(d.val:Word w))=
      ((S.compact+GridApproximationAdvice.portBase X+(3*i.val+d.val):ℕ):Word w) := by
    simp [GridApproximationAdvice.portBase,GridApproximationAdvice.rowBase]; ring
  rw [eq,Fin.val_cast_of_lt addr,mounted.tags]

set_option maxRecDepth 32000 in
omit [Field F] [Fintype F] in
theorem body_at (S : Banks) (B : ℕ) (m : Memory w) (mounted : Mounted X P S B m)
    (fit : Fits (n:=n) (w:=w) X S B) (c : Cell k n) (j : Catalyst.Port p X.width) :
    (body (n+1)).eval (words S B k p r (n+1)) m
      ![((finFunctionFinEquiv c).val:Word w),((Fintype.equivFin _ j).val:Word w)] =
      (ptr (sourcePin P P.data c j):Word w) := by
  let old := Fintype.equivFin _ j
  have f (d : Fin 3) := load_field X P S B m mounted fit c old d
  simp only [old,Equiv.symm_apply_apply] at f
  have f₀ := f ⟨0,by decide⟩
  have f₁ := f ⟨1,by decide⟩
  have f₂ := f ⟨2,by decide⟩
  simp only [] at f₀ f₁ f₂
  rw [body_eval]
  cases j with
  | inl z =>
    have loc := (below (base:=S.data) (finFunctionFinEquiv c) z).trans_le fit.data
    change _ = (0 : Word w) at f₀
    rw [f₀,ite_eq_left rfl,data_eval,f₂]
    change m (((S.data:Word w)+(((finFunctionFinEquiv c).val:Word w)*(p:Word w)+(z.val:Word w))).val)=_
    rw [←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add,Fin.val_cast_of_lt loc,mounted.localData]
  | inr u =>
    rcases u with ⟨⟨j,i⟩,b⟩
    let z : Catalyst.Wire X.width := ⟨j,i⟩
    let v := finFunctionFinEquiv c
    have ordFit := v.isLt.trans fit.cells
    have sFit : (n+1)^j.val < 2^w :=
      (Nat.pow_le_pow_right (Nat.succ_pos _) j.isLt.le).trans_lt fit.cells
    have ca := fit.chosen
    have si := fit.stride
    have strideFit : S.stride+j.val < 2^w := by have := j.isLt; omega
    let bin : Fin (((n+1)^k)*k) := finProdFinEquiv (v,j)
    have bn : bin.val=v.val*k+j.val := by simp [bin,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have railFit : S.chosen+((v.val*k+j.val)*B+i.val) < 2^w := by
      rw [←bn]
      exact (below bin (i.castLE (fit.widths j))).trans_le ca
    have found : useRail.eval (words S B k p r (n+1)) m
        ![(v.val:Word w),((Fintype.equivFin (Catalyst.Port p X.width) (Sum.inr (z,b))).val:Word w)] =
        ((P.pass c z).val:Word w) := by
      rw [rail_eval,f₁,f₂]
      change m (((S.chosen:Word w)+(((v.val:Word w)*(k:Word w)+(j.val:Word w))*(B:Word w)+(i.val:Word w))).val)=_
      rw [←Nat.cast_mul,←Nat.cast_add,←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add,
        Fin.val_cast_of_lt railFit]
      exact mounted.chosenRail c z
    have dig : (BinaryOp.eval .mod (bitIndex.eval (words S B k p r (n+1)) m
        ![(v.val:Word w),((Fintype.equivFin (Catalyst.Port p X.width) (Sum.inr (z,b))).val:Word w)]) ((n+1:ℕ):Word w)) =
        ((c j).val:Word w) := by
      have lng := GridLens.ordinal_digit c j
      rw [bit_eval,f₁]
      change Fin.ofNat _ ((Fin.ofNat (2^w) (((v.val:Word w).val) /
        (m (((S.stride:Word w)+(j.val:Word w)).val)).val)).val % (((n+1:ℕ):Word w).val)) = _
      have strideWord : m (S.stride+j.val) = (((n+1)^j.val : ℕ) : Word w) := by
        simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using mounted.stride j
      rw [←Nat.cast_add,Fin.val_cast_of_lt strideFit,strideWord,Fin.val_cast_of_lt ordFit,
        Fin.val_cast_of_lt sFit]
      have qf : v.val/(n+1)^j.val < 2^w := (Nat.div_le_self ..).trans_lt ordFit
      simp only [Fin.val_ofNat,Nat.mod_eq_of_lt qf,Fin.val_cast_of_lt fit.grid]
      change Fin.ofNat (2^w) ((finFunctionFinEquiv c).val/(n+1)^j.val%(n+1)) = _
      rw [lng]; apply Fin.ext;
        simp only [Fin.val_ofNat,Nat.mod_eq_of_lt ((c j).isLt.trans fit.grid),
          Fin.val_cast_of_lt ((c j).isLt.trans fit.grid)]
    have two : 2 < 2^w := by
      have := fit.compact
      unfold GridApproximationAdvice.multBase GridApproximationAdvice.portBase GridApproximationAdvice.rowBase at this
      omega
    have tag : ((1+b.toNat:ℕ):Word w)≠0 := by
      have bitBound : b.toNat ≤ 1 := by cases b <;> decide
      have h : 1+b.toNat < 2^w := by omega
      intro zero
      have v' := congrArg Fin.val zero
      rw [Fin.val_cast_of_lt h,Fin.val_zero] at v'
      omega
    change _ = ((1+b.toNat : ℕ) : Word w) at f₀
    dsimp only [z,v] at found dig
    rw [f₀,ite_eq_right tag,found,dig]
    simp [words,sourcePin,ptr,Wiring.source,sourceAddress,hiddenBase,port,port_number,P.pass_dir]
    ring

def build (S : Banks) (B k p r n w : ℕ) : PhysicalProcedure.Procedure w :=
  PhysicalInputPhases.writing (program ((n+1)^k) (n+1)) (words S B k p r (n+1)) S.output (((n+1)^k)*B)

/-- Exact value of the densely numbered port bank. The unused tail of its public
allocation is zero. -/
noncomputable def imageWord (S : Banks) (a : ℕ) : Word w :=
  let q := GridApproximationAdvice.portCount X
  let x := a-S.output
  if h : x < (n+1)^k*q then
    let i : Fin ((n+1)^k*q) := ⟨x,h⟩
    let ci := finProdFinEquiv.symm i
    (sourceAddress ((wiring P).copyInput ci.1 ci.2):Word w)
  else 0

omit [Field F] [Fintype F] in
theorem imageWord_at (S : Banks) (c : Fin ((n+1)^k)) (i : Fin (GridApproximationAdvice.portCount X)) :
    imageWord X P S (S.output+c.val*(GridApproximationAdvice.portCount X)+i.val) =
      (sourceAddress ((wiring P).copyInput c i):Word w) := by
  let z := finProdFinEquiv (c,i)
  have number : z.val=c.val*(GridApproximationAdvice.portCount X)+i.val := by
    simp [z,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have off : S.output+c.val*(GridApproximationAdvice.portCount X)+i.val-S.output=z.val := by omega
  simp only [imageWord,off,dite_eq_left z.isLt]
  change (sourceAddress ((wiring P).copyInput (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2):Word w)=_
  simp [z]

omit [Field F] [Fintype F] in
theorem program_at (S : Banks) (B : ℕ) (m : Memory w) (mounted : Mounted X P S B m)
    (fit : Fits (n:=n) (w:=w) X S B) (a : Word w)
    (lo : S.output ≤ a.val) (_hi : a.val < S.output+(n+1)^k*B) :
    (program ((n+1)^k) (n+1)).eval (words S B k p r (n+1)) m (fun _=>a) =
      imageWord X P S a.val := by
  let q := GridApproximationAdvice.portCount X
  let L := (n+1)^k
  let x := a.val-S.output
  let param := words (w:=w) S B k p r (n+1)
  let v : Fin 1 → Word w := fun _=>a
  have head : S.compact+4 < 2^w := by
    have h := fit.compact
    unfold GridApproximationAdvice.multBase GridApproximationAdvice.portBase GridApproximationAdvice.rowBase at h
    omega
  have read : (header (w:=w) (v:=1) 4).eval param m v=(q:Word w) := by
    change m (((S.compact:Word w)+4).val)=_
    rw [show (S.compact:Word w)+4=((S.compact+4:ℕ):Word w) by simp,
      Fin.val_cast_of_lt head,mounted.ports]
  have off : offset.eval param m v=(x:Word w) := by
    change a-(S.output:Word w)=((a.val-S.output:ℕ):Word w)
    rw [Nat.cast_sub lo,Fin.cast_val_eq_self]
  have half : L*q ≤ L*B := Nat.mul_le_mul_left L fit.ports
  have countFit : L*q < 2^w := by have := fit.output; change S.output+L*B < 2^w at this; omega
  have idxFit : x < 2^w := (Nat.sub_le a.val _).trans_lt a.isLt
  have qFit : q < 2^w := fit.ports.trans_lt fit.cap
  have branch : Comparison.test .lt (offset.eval param m v) ((mul (val L) (header 4)).eval param m v) =
      decide (x < L*q) := by
    rw [off]
    simp [Term.eval_binary,Term.eval_literal,read,Comparison.test,BinaryOp.eval,←Nat.cast_mul,
      Fin.lt_def,Fin.val_cast_of_lt idxFit,Fin.val_cast_of_lt countFit]
  change (program L (n+1)).eval param m v=_
  unfold program
  rw [Term.eval_select,branch]
  by_cases live : x < L*q
  · rw [ite_eq_left (by simp [live])]
    let z : Fin (L*q) := ⟨x,live⟩
    let ci : Fin L × Fin q := finProdFinEquiv.symm z
    have num : x=ci.1.val*q+ci.2.val := by
      have e := congrArg Fin.val (finProdFinEquiv.apply_symm_apply z)
      simpa [ci,z,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using e.symm
    have dv : x/q=ci.1.val := by rw [num,Nat.mul_comm _ q,Nat.mul_add_div (Nat.zero_lt_of_lt ci.2.isLt),
        Nat.div_eq_of_lt ci.2.isLt,Nat.add_zero]
    have md : x%q=ci.2.val := by simp [num,Nat.mod_eq_of_lt ci.2.isLt]
    unfold raw
    rw [Term.eval_instantiate]
    have vars : (fun i => ((![.binary .div offset (header 4),.binary .mod offset (header 4)] :
        Fin 2 → Q w) i).eval param m v)=![(ci.1.val:Word w),(ci.2.val:Word w)] := by
      funext i
      fin_cases i <;> simp [Term.eval_binary,off,read,BinaryOp.eval,Fin.val_cast_of_lt idxFit,
        Fin.val_cast_of_lt qFit,dv,md]
    rw [vars]
    have loc : a.val=S.output+ci.1.val*q+ci.2.val := by dsimp [x] at num; omega
    rw [loc,imageWord_at]
    simpa [ptr,UniversalGrid.Wiring.copyInput,wiring,emit,param,L,q] using
      body_at X P S B m mounted fit (finFunctionFinEquiv.symm ci.1) ((Fintype.equivFin _).symm ci.2)
  · rw [ite_eq_right (by simpa using live)]
    unfold imageWord
    rw [dite_eq_right live]; rfl

structure Separate (S : Banks) (L B : ℕ) : Prop where
  compact : S.output+L*B ≤ S.compact ∨ S.compact+GridApproximationAdvice.multBase X ≤ S.output
  data : S.output+L*B ≤ S.data
  chosen : S.output+L*B ≤ S.chosen
  stride : S.output+L*B ≤ S.stride

omit [Field F] [Fintype F] in
theorem build_spec (S : Banks) (B : ℕ) (fit : Fits (n:=n) (w:=w) X S B)
    (away : Separate X S ((n+1)^k) B) :
    (build S B k p r n w).Spec (Mounted X P S B)
      (fun m o => o=fillSegment S.output (((n+1)^k)*B) (imageWord X P S) m)
      (4+((n+1)^k)*B*(2*(program (w:=w) ((n+1)^k) (n+1)).binds+4)) := by
  apply PhysicalInputPhases.writing_spec _ _ _ _ fit.output
  intro initial ok a m lo hi frame
  apply program_at X P S B m _ fit a lo hi
  have compact (off : ℕ) (inBank : off < GridApproximationAdvice.multBase X) :
      m (S.compact+off)=initial (S.compact+off) :=
    frame _ (by rcases away.compact with hi|lo <;> omega)
  have hdr (j : Fin 6) : j.val < GridApproximationAdvice.multBase X := by
    have := j.isLt
    unfold GridApproximationAdvice.multBase GridApproximationAdvice.portBase GridApproximationAdvice.rowBase
    omega
  constructor
  · exact (compact 3 (hdr 3)).trans ok.cells
  · exact (compact 4 (hdr 4)).trans ok.ports
  · intro i j
    rw [Nat.add_assoc,compact (GridApproximationAdvice.portBase X+(3*i.val+j.val)) (by
      have := below (base:=GridApproximationAdvice.portBase X) i j
      unfold GridApproximationAdvice.multBase
      nlinarith),←Nat.add_assoc,ok.tags]
  · intro c i; exact (frame _ (.inr (by have := away.data; omega))).trans (ok.localData c i)
  · intro c z; exact (frame _ (.inr (by have := away.chosen; omega))).trans (ok.chosenRail c z)
  · intro j; exact (frame _ (.inr (by have := away.stride; omega))).trans (ok.stride j)

set_option maxRecDepth 32000 in
theorem time_per_port (L g : ℕ) : (program (w:=w) L g).binds ≤ 600 := by
  simp [program,raw,Term.binds_instantiate,Fin.sum_univ_succ,body,dataPtr,bitIndex,offset,
    useRail,header,field,descriptorBase,load,add,mul,val,Term.select,Term.load,Term.parameter,
    Term.literal,Term.binary,Term.binds]

end Hierarchy.GridOrderedPinsRAM

end OAI
