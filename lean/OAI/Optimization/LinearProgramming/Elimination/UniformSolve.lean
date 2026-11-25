import OAI.Optimization.LinearProgramming.Elimination.UniformRowBasis
import OAI.Optimization.LinearProgramming.Elimination.UniformInverseVector
import OAI.Optimization.LinearProgramming.Elimination.Augmented
import OAI.Optimization.LinearProgramming.Elimination.SolveEquiv
import OAI.Optimization.LinearProgramming.Geometry.GramEncoding
import OAI.Optimization.LinearProgramming.Elimination.UniformValues

/-! One fixed program for arbitrary rectangular systems. The ordinary tape consists of the
right-hand side, followed by the columns of the input matrix. The first returned flag is one
for inconsistency. Otherwise the following `d` output coordinates give the canonical solution. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM _root_.OAI.Optimization.LinearProgramming.Geometry Compression Matrix
open scoped Matrix BigOperators

def uniformSolveBlock : Block := .seq uniformRowBasisBlock (.seq rebuildMask (.seq uniformGramInversePhase uniformInverseVector))

/-- Empty equation lists halt directly. This keeps scalar bit lengths independent of a
variable dimension whose columns have no scalar entries. -/
def guardedSolveBlock : Block := .branch (.addrLT 14 1) uniformSolveBlock .skip

def uniformSolveProgram : Program := guardedSolveBlock.compile 0 ++ [.halt 0]

def solveCoreTime (d m : ℕ) := let r:=d+1
  rowBasisTime r m + (maskTableCost r+100*(r+1)^2 + (gramInverseTime r+inverseVectorTime r))

def solveTime (d m : ℕ) := solveCoreTime d m+2

/-- The output convention uses an inconsistency flag and the contiguous solution subarray. -/
def readSolution {K : Type} [Zero K] [DecidableEq K] {d m : ℕ} (l : GramLayout (d+1) m) (s : Memory K) : Option (Fin d→K) :=
  if s.data l.inv=0 then some (fun j=>s.data (l.workB+j.succ.val)) else none

/-- Caller-visible output convention using only the runtime address bank. -/
def readSolutionFromHeader {K : Type} [Zero K] [DecidableEq K] (d : ℕ) (s : Memory K) : Option (Fin d→K) :=
  if s.data (s.index 62)=0 then some (fun j=>s.data (s.index 63+j.succ.val)) else none

/-- The single ROM emits the same solution as the dynamic executable, including the
precise canonical choice in underdetermined systems. The predicate holds at every time. -/
theorem uniformSolveBlock_safe {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (P : K→Prop)
    (values : SolveValues P (augmentedRows A b))
    (hinput : ∀i : ℕ,P ((encodedGramInput (augmentedRows A b))[i]?.getD 0)) :
    let input := encodedGramInput (augmentedRows A b)
    ∃t c,c+1 ≤ solveCoreTime d m ∧ Block.Eval (Memory.AllData P) uniformSolveBlock
      (start [d+1,m] input).memory c t ∧ readSolution (packedGramLayout (d+1) m) t=solve A b ∧
      t.index 62=(packedGramLayout (d+1) m).inv ∧ t.index 63=(packedGramLayout (d+1) m).workB := by
  let T := augmentedRows A b
  let r := d+1
  let input := encodedGramInput T
  let l := packedGramLayout r m
  let G := T*Tᵀ
  let S := basisMask G
  let M := maskGram G (flag S)
  have enc : rectangularTape r m input=T := gramInputMatrix_encoded T
  obtain ⟨u,k,hk,e,hu,hhead,_⟩ := uniformRowBasisBlock_safe r m input P hinput values.zero values.one values.neg
    (by rw [enc];exact values.gram) (by rw [enc];exact values.masks)
  rw [enc] at hu
  have hS : BasisState (layoutForGram l) G S u := by
    change BasisState (layoutForGram l) (T*Tᵀ) (scanMask (T*Tᵀ) (List.finRange r)) u
    simpa only [visitedBasis_full] using hu
  obtain ⟨v,c,hc,ev,hv⟩ := rebuildMask_spec l G S P u hS hhead e.safe_end values.zero values.one
  have hli := (scanMask_spec Tᵀ (List.finRange r)).1
  have hm : M.det≠0 := by
    have dh:=maskGram_det_ne_zero_iff Tᵀ S
    rw [Matrix.transpose_transpose,determinant_eq] at dh
    apply dh.mpr
    change LinearIndepOn K Tᵀ.col (scanMask (T*Tᵀ) (List.finRange r) : Set (Fin r))
    simpa only [Matrix.transpose_transpose] using hli
  have mval : uniformRect r r (inverseLayout l).g v=M := hv.masked
  obtain ⟨w,j,hj,ew,inv,iw⟩ := uniformGramInversePhase_spec (inverseLayout l) P v hv.source.layout ev.safe_end
    values.zero values.one values.neg (by rw [mval];exact hm) (by rw [mval];exact values.reciprocal)
    (by rw [mval];exact values.cofactors) (by rw [mval];exact values.inverse)
  rw [mval] at inv
  have low:=l.minimum;have dt:=l.d_tr;have tg:=l.tr_g;have gi:=l.g_inv;have il:=l.inv_left
  have ll:=l.left_out;have os:=l.out_sub;have sa:=l.sub_workA;have ab:=l.workA_workB;have r2:=Nat.le_mul_self r
  have wG : uniformRect r r l.g w=G := by
    apply Eq.trans _ hv.gram
    ext i jj
    have h:=rectOffset_lt i jj
    exact iw.data (l.g+i.val*r+jj.val) (by omega)
      (Or.inl (by change l.g+i.val*r+jj.val < l.workA;omega))
      (Or.inl (by change l.g+i.val*r+jj.val < l.workB;omega))
  have wS (i : Fin r) : w.data (l.inv+i.val)=flag S i := (iw.data (l.inv+i.val) (by omega)
    (Or.inl (by change l.inv+i.val < l.workA;omega)) (Or.inl (by change l.inv+i.val < l.workB;omega))).trans (hv.flags i)
  obtain ⟨t,q,hq,eq,vx,flags,hret⟩ := uniformInverseVector_spec l G M⁻¹ S P w 0 rfl
    (hv.source.of_frame iw.index) ew.safe_end wG inv wS values.zero values.apply
  have cost : k+(c+(j+q))+1 ≤ rowBasisTime r m +
      (maskTableCost r+100*(r+1)^2+(gramInverseTime r+inverseVectorTime r)) := by omega
  refine ⟨t,k+(c+(j+q)),cost,e.seq (ev.seq (ew.seq eq)),?_,hret.flags,hret.result⟩
  have fz : t.data l.inv=flag S 0 := by simpa only [Fin.val_zero,Nat.add_zero] using flags 0
  change (if t.data l.inv=0 then some (fun i : Fin d=>t.data (l.workB+i.succ.val)) else none)=solve A b
  rw [fz]
  by_cases hb : (0 : Fin r) ∈ S
  · rw [show (flag S 0 : K)=1 by simp [flag,hb],ite_eq_right one_ne_zero]
    symm;apply (solve_none_iff A b).2;intro existsSol;exact ((augmented_basis A b).1.2 existsSol) hb
  · rw [show (flag S 0 : K)=0 by simp [flag,hb],ite_eq_left rfl]
    obtain ⟨x,hx⟩:=solve_complete A b ((augmented_basis A b).1.mp hb)
    rw [hx];congr 1;funext i
    have hsup (p : Fin d) (hp : p∉basisMask (Aᵀ*A)) : x p=0 := solve_zero_off_basis A b x hx p
      (by simpa [basisMask_eq_columnBasis] using hp)
    exact (vx i.succ).trans (augmented_recovery A b x (solve_sound A b x hx) hsup i)

/-- The zero-row branch has a two-step trace, and all its scalars are zero. -/
theorem uniformSolveProgram_noRows {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {d : ℕ}
    (A : Matrix (Fin 0) (Fin d) K) (b : Fin 0→K) :
    let input := encodedGramInput (augmentedRows A b)
    ∃tr : Fin (2+1)→State K,Trace uniformSolveProgram (start [d+1,0] input) 2 tr ∧
      (tr (Fin.last 2)).output=some 0 ∧ readSolution (packedGramLayout (d+1) 0) (tr (Fin.last 2)).memory=solve A b ∧
      readSolutionFromHeader d (tr (Fin.last 2)).memory=solve A b ∧ ∀i p,(tr i).data p=0 := by
  let input := encodedGramInput (augmentedRows A b)
  have nil : input=[] := List.length_eq_zero_iff.mp (by simp [input])
  let m:=(start [d+1,0] input).memory
  have hm : m.AllData (fun x=>x=0) := by intro i;simp [m,nil,start,State.memory]
  have e : Block.Eval (Memory.AllData (fun x=>x=0)) guardedSolveBlock m 1 m :=
    .branchFalse (by simp [Cond.test,m,start,State.memory]) (.skip hm)
  obtain ⟨tr,ht,halt,mem,safe⟩:=e.halted_trace (tag:=0)
  have hsol : solve A b=some 0 := (fixedSolve_eq_solve A b).symm.trans <|
    fixedSolve_of_supported A b 0 (by funext i;exact Fin.elim0 i) (fun _ _=>rfl)
  have dataZero (i : ℕ) : m.data i=0 := hm i
  have zeroFun : (fun _ : Fin d => (0 : K))=(0 : Fin d→K) := funext fun _=>rfl
  refine ⟨tr,ht,halt,?_,?_,safe⟩
  · rw [mem,hsol];simp [readSolution,dataZero];exact zeroFun
  · rw [mem,hsol];simp [readSolutionFromHeader,dataZero];exact zeroFun

theorem uniformSolveProgram_safe {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (P : K→Prop)
    (values : SolveValues P (augmentedRows A b))
    (hinput : ∀i : ℕ,P ((encodedGramInput (augmentedRows A b))[i]?.getD 0)) :
    let input := encodedGramInput (augmentedRows A b)
    ∃ k ≤ solveTime d m,∃tr : Fin (k+1)→State K,
      Trace uniformSolveProgram (start [d+1,m] input) k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      readSolution (packedGramLayout (d+1) m) (tr (Fin.last k)).memory=solve A b ∧
      readSolutionFromHeader d (tr (Fin.last k)).memory=solve A b ∧ ∀i p,P ((tr i).data p) := by
  cases m with
  | zero =>
    obtain ⟨tr,ht,hh,out,outH,hz⟩:=uniformSolveProgram_noRows A b
    exact ⟨2,by unfold solveTime;omega,tr,ht,hh,out,outH,fun i p=>(hz i p) ▸ values.zero⟩
  | succ m =>
    obtain ⟨t,k,hk,run,out,flagP,vecP⟩:=uniformSolveBlock_safe A b P values hinput
    have e : Block.Eval (Memory.AllData P) guardedSolveBlock _ (1+k+1) t :=
      .branchTrue (by simp [Cond.test,start,State.memory]) run
    obtain ⟨tr,ht,halt,mem,safe⟩:=e.halted_trace (tag:=0)
    refine ⟨_,by unfold solveTime;omega,tr,ht,halt,by rw [mem];exact out,?_,safe⟩
    rw [mem];simpa only [readSolutionFromHeader,flagP,vecP,readSolution] using out

theorem uniformSolveProgram_orderedField {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) :
    ∃k ≤ solveTime d m,∃tr : Fin (k+1)→State K,
      Trace uniformSolveProgram (start [d+1,m] (encodedGramInput (augmentedRows A b))) k tr ∧
      (tr (Fin.last k)).output=some 0 ∧ readSolution (packedGramLayout (d+1) m) (tr (Fin.last k)).memory=solve A b := by
  obtain ⟨k,hk,tr,ht,halt,out,_⟩:=uniformSolveProgram_safe A b (fun _=>True)
    ⟨trivial,trivial,fun _ _=>trivial,fun _ _ _=>trivial,fun _ _ _ _=>trivial,trivial,
      fun _ _ _ _=>trivial,fun _ _=>trivial,fun _ _=>trivial⟩ (fun _=>trivial)
  exact ⟨k,hk,tr,ht,halt,out⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
