import OAI.Optimization.LinearProgramming.PrimalDual.CopyRAM

/-! A unit-cost streaming kernel for coordinate differences, dot products, and
division by the certified nonzero ray objective. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Tape RAM.Block

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

inductive OutputPass
  | dot | difference | normalize
  deriving DecidableEq

namespace OutputPass

variable {F : Type*}

def returned [Field F] (p : OutputPass) (a b acc : F) : F :=
  match p with
  | .dot => a*b
  | .difference => a-b
  | .normalize => a/acc

def nextAccumulator [Field F] (p : OutputPass) (acc value : F) : F :=
  if p = .dot then acc+value else acc

private def right (p : OutputPass) : Instr :=
  if p = .normalize then .copy 1 3 else .load 1 1

private def calculate : OutputPass → Instr
  | .dot => .mul 0 0 1
  | .difference => .sub 0 0 1
  | .normalize => .div 0 0 1

private def output (p : OutputPass) : Instr :=
  if p = .dot then .add 3 3 0 else .store 2 0

/-- Address registers 0,1,2 point to left source, right source, and destination.
Only dot updates scalar 3 (the accumulator); normalize reads scalar 3 as divisor. -/
def cell (p : OutputPass) : Block := .straight [.load 0 0, p.right, p.calculate, p.output]

private def value (p : OutputPass) (s : Memory K) : K :=
  p.returned (s.data (s.index 0)) (s.data (s.index 1)) (s.data 3)

theorem cell_correct (p : OutputPass) (s : Memory K) (hs : Good P s)
    (hr : 4 ≤ s.index 1) (hd : 4 ≤ s.index 2) (hdiv : p = .normalize → s.data 3 ≠ 0)
    (hv : P (p.value s)) (ha : P (p.nextAccumulator (s.data 3) (p.value s))) :
    ∃ t, Eval (Good P) (p.cell) s 4 t ∧ t.index = s.index ∧
      t.data 3 = p.nextAccumulator (s.data 3) (p.value s) ∧
      ∀ k, 4 ≤ k → t.data k = if p ≠ .dot ∧ k = s.index 2 then p.value s else s.data k := by
  let x := s.data (s.index 0)
  let y := if p = .normalize then s.data 3 else s.data (s.index 1)
  let s1 := s.putData 0 x
  let s2 := s1.putData 1 y
  let s3 := s2.putData 0 (p.value s)
  have h1 : Good P s1 := safe_data_write s hs _ _ (hs _)
  have h2 : Good P s2 := safe_data_write s1 h1 _ _ (by dsimp [y]; split <;> exact hs _)
  have h3 : Good P s3 := safe_data_write s2 h2 _ _ hv
  have a : Eval (Good P) (.op (.load 0 0)) s 1 s1 := Eval.op_load s _ _ hs h1
  have rightLoad : s1.data (s1.index 1) = s.data (s.index 1) := by
    change (s.putData 0 x).data (s.index 1) = _
    exact Memory.putData_ne s (by omega : s.index 1 ≠ 0) x
  have rightCopy : s1.data 3 = s.data 3 := Memory.putData_ne s (by decide) _
  have b : Eval (Good P) (.op p.right) s1 1 s2 := by
    by_cases hp : p = .normalize
    · have he := Eval.op_copy s1 1 3 h1 (safe_data_write _ h1 _ _ (h1 _))
      simpa only [right, hp, ↓reduceIte, s2, y, rightCopy] using he
    · have he := Eval.op_load s1 1 1 h1 (safe_data_write _ h1 _ _ (h1 _))
      simpa only [right, hp, ↓reduceIte, s2, y, rightLoad] using he
  have leftVal : s2.data 0 = x := by simp [s2,s1]
  have rightVal : s2.data 1 = y := by simp [s2]
  have c : Eval (Good P) (.op p.calculate) s2 1 s3 := by
    cases p with
    | dot =>
      have eq : s2.data 0 * s2.data 1 = OutputPass.dot.value s := by rw [leftVal,rightVal]; rfl
      simpa only [calculate,s3,eq] using Eval.op_mul s2 0 0 1 h2 (safe_data_write _ h2 _ _ (eq ▸ hv))
    | difference =>
      have eq : s2.data 0 - s2.data 1 = OutputPass.difference.value s := by rw [leftVal,rightVal]; rfl
      simpa only [calculate,s3,eq] using Eval.op_sub s2 0 0 1 h2 (safe_data_write _ h2 _ _ (eq ▸ hv))
    | normalize =>
      have eq : s2.data 0 / s2.data 1 = OutputPass.normalize.value s := by rw [leftVal,rightVal]; rfl
      have nz : s2.data 1 ≠ 0 := by rw [rightVal]; exact hdiv rfl
      simpa only [calculate,s3,eq] using Eval.op_div s2 0 0 1 nz h2 (safe_data_write _ h2 _ _ (eq ▸ hv))
  have atZero : s3.data 0 = p.value s := by simp [s3]
  have atThree : s3.data 3 = s.data 3 := by simp [s3,s2,s1]
  have frame (k : Nat) (hk : 4 ≤ k) : s3.data k = s.data k := by
    simp only [s3,s2,s1,Memory.putData_ne _ (by omega : k ≠ 0), Memory.putData_ne _ (by omega : k ≠ 1)]
  by_cases hp : p = .dot
  · let t := s3.putData 3 (s.data 3+p.value s)
    have eq : s3.data 3+s3.data 0 = s.data 3+p.value s := by rw [atZero,atThree]
    have ok : P (s3.data 3+s3.data 0) := by simpa [eq,nextAccumulator,hp] using ha
    have d : Eval (Good P) (.op p.output) s3 1 t := by
      simpa only [output,hp,↓reduceIte,t,eq] using Eval.op_add s3 3 3 0 h3 (safe_data_write _ h3 _ _ ok)
    refine ⟨t,a.seq (b.seq (c.seq (d.seq (.skip d.safe_end)))),rfl,?_,?_⟩
    · simp [t,nextAccumulator,hp]
    · intro k hk
      simpa [t,hp,Memory.putData_ne _ (by omega : k ≠ 3)] using frame k hk
  · let t := s3.putData (s.index 2) (p.value s)
    have d : Eval (Good P) (.op p.output) s3 1 t := by
      simpa only [output,hp,↓reduceIte,t,atZero,s3,s2,s1,Memory.putData_index] using
        Eval.op_store s3 2 0 h3 (safe_data_write _ h3 _ _ (h3 _))
    refine ⟨t,a.seq (b.seq (c.seq (d.seq (.skip d.safe_end)))),rfl,?_,?_⟩
    · simp [t,Memory.putData_ne _ (by omega : 3 ≠ s.index 2),atThree,nextAccumulator,hp]
    · intro k hk; by_cases h : k = s.index 2
      · subst k; simp [t,hp]
      · simpa [t,h,hp,Memory.putData_ne] using frame k hk

private def shift : Block := .straight [.incr 0 0, .incr 1 1, .incr 2 2]

private theorem shift_correct (s : Memory K) (hs : Good P s) :
    ∃ t, Eval (Good P) shift s 3 t ∧ t.data = s.data ∧
      t.index 0 = s.index 0+1 ∧ t.index 1 = s.index 1+1 ∧ t.index 2 = s.index 2+1 ∧
      ∀ k, 3 ≤ k → t.index k = s.index k := by
  let s1 := s.putIndex 0 (s.index 0+1)
  let s2 := s1.putIndex 1 (s.index 1+1)
  let t := s2.putIndex 2 (s.index 2+1)
  have a : Eval (Good P) (.op (.incr 0 0)) s 1 s1 := eval_incr s hs 0 0
  have b : Eval (Good P) (.op (.incr 1 1)) s1 1 s2 := by simpa [s1,s2] using eval_incr s1 a.safe_end 1 1
  have c : Eval (Good P) (.op (.incr 2 2)) s2 1 t := by simpa [s2,s1,t] using eval_incr s2 b.safe_end 2 2
  refine ⟨t,a.seq (b.seq (c.seq (.skip c.safe_end))),rfl,by simp [t,s2,s1],by simp [t,s2],by simp [t],?_⟩
  intro k hk
  simp [t,s2,s1,Memory.putIndex_ne _ (by omega : k ≠ 2), Memory.putIndex_ne _ (by omega : k ≠ 1),
    Memory.putIndex_ne _ (by omega : k ≠ 0)]

/-- Iterate a pass over n cells. Address register 5 holds n, and register 4
is the loop counter. All address registers above 5 survive. -/
def scan (p : OutputPass) : Block := .forRange 4 5 (.seq p.cell shift)
private structure ScanInv (p : OutputPass) (n a b dst : Nat) (initial : Memory K)
    (acc result : Nat → K) (j : Nat) (s : Memory K) (P : K → Prop) : Prop where
  safe : Good P s
  ptrA : s.index 0 = a+j
  ptrB : s.index 1 = b+j
  ptrOut : s.index 2 = dst+j
  counter : s.index 4 = j
  size : s.index 5 = n
  indices : ∀ k, 6 ≤ k → s.index k = initial.index k
  accum : s.data 3 = acc j
  left : ∀ k, j ≤ k → k < n → s.data (a+k) = initial.data (a+k)
  right : ∀ k, j ≤ k → k < n → s.data (b+k) = initial.data (b+k)
  done : ∀ k < j, p ≠ .dot → s.data (dst+k) = result k
  frame : ∀ k, 4 ≤ k → (p = .dot ∨ k < dst ∨ dst+n ≤ k) → s.data k = initial.data k

/-- Exact execution of a complete numerical pass. Source and destination windows
may coincide exactly, as when normalizing a vector in place. All other overlaps
are excluded for writing passes. -/
theorem scan_correct (p : OutputPass) (n a b dst : Nat) (s : Memory K) (hs : Good P s)
    (hA : s.index 0 = a) (hB : s.index 1 = b) (hD : s.index 2 = dst) (hsz : s.index 5 = n)
    (ha : 4 ≤ a) (hb : 4 ≤ b) (hd : 4 ≤ dst)
    (sepA : p = .dot ∨ a = dst ∨ a+n ≤ dst ∨ dst+n ≤ a)
    (sepB : p = .dot ∨ b = dst ∨ b+n ≤ dst ∨ dst+n ≤ b)
    (acc result : Nat → K) (acc0 : s.data 3 = acc 0)
    (hv : ∀ j < n, result j = p.returned (s.data (a+j)) (s.data (b+j)) (acc j))
    (hn : ∀ j < n, acc (j+1) = p.nextAccumulator (acc j) (result j))
    (hdiv : ∀ j < n, p = .normalize → acc j ≠ 0)
    (hvSafe : ∀ j < n, P (result j)) (haSafe : ∀ j ≤ n, P (acc j)) :
    ∃ t, Eval (Good P) p.scan s (10*n+2) t ∧
      t.data 3 = acc n ∧ (∀ k < n, p ≠ .dot → t.data (dst+k) = result k) ∧
      (∀ k, 4 ≤ k → (p = .dot ∨ k < dst ∨ dst+n ≤ k) → t.data k = s.data k) ∧
      (∀ k, 6 ≤ k → t.index k = s.index k) := by
  let I := fun j w => ScanInv p n a b dst s acc result j w P
  have hi : I 0 (s.putIndex 4 0) :=
    ⟨hs,by simpa using hA,by simpa using hB,by simpa using hD,by simp,by simpa using hsz,
      fun k hk => Memory.putIndex_ne _ (by omega) _,acc0,fun _ _ _ => rfl,fun _ _ _ => rfl,
      fun _ hj => (Nat.not_lt_zero _ hj).elim,fun _ _ _ => rfl⟩
  have body (j : Nat) (hj : j<n) (w : Memory K) (hw : I j w) :
      ∃ t, Eval (Good P) (.seq p.cell shift) w 7 t ∧ I (j+1) (t.putIndex 4 (t.index 4+1)) := by
    have eqv : p.value w = result j := by
      dsimp only [value]
      rw [hw.ptrA,hw.ptrB,hw.left j le_rfl hj,hw.right j le_rfl hj,hw.accum,← hv j hj]
    have eqa : p.nextAccumulator (w.data 3) (p.value w) = acc (j+1) := by
      rw [hw.accum,eqv,hn j hj]
    obtain ⟨t0,cellRun,ind0,acc'0,fr0⟩ := cell_correct p w hw.safe
      (hw.ptrB ▸ by omega) (hw.ptrOut ▸ by omega)
      (fun e => hw.accum ▸ hdiv j hj e) (eqv ▸ hvSafe j hj) (eqa ▸ haSafe (j+1) hj)
    obtain ⟨t,sh,hd',ia,ib,idst,ifront⟩ := shift_correct t0 cellRun.safe_end
    let t' := t.putIndex 4 (t.index 4+1)
    have at' (k) (hk : 4 ≤ k) : t'.data k =
        if p ≠ .dot ∧ k=dst+j then result j else w.data k := by
      change t.data k = _; rw [hd',fr0 k hk,hw.ptrOut,eqv]
    have above (k : Nat) (hk : 5 ≤ k) : t'.index k = w.index k := by
      change (t.putIndex 4 _).index k = _
      rw [Memory.putIndex_ne _ (by omega : k ≠ 4),ifront k (by omega),ind0]
    refine ⟨t,cellRun.seq sh,sh.safe_end,?_,?_,?_,?_,(above 5 le_rfl).trans hw.size,
      fun k hk => (above k (by omega)).trans (hw.indices k hk),?_,?_,?_,?_,?_⟩
    · change t.index 0 = a+(j+1); rw [ia,ind0,hw.ptrA]; omega
    · change t.index 1 = b+(j+1); rw [ib,ind0,hw.ptrB]; omega
    · change t.index 2 = dst+(j+1); rw [idst,ind0,hw.ptrOut]; omega
    · rw [Memory.putIndex_same,ifront 4 (by decide),ind0,hw.counter]
    · change t.data 3 = _
      rw [hd',acc'0,eqa]
    · intro k hjk hkn; rw [at' _ (by omega),ite_eq_right (by rcases sepA with h|h|h|h <;> simp_all <;> omega)]
      exact hw.left k (by omega) hkn
    · intro k hjk hkn; rw [at' _ (by omega),ite_eq_right (by rcases sepB with h|h|h|h <;> simp_all <;> omega)]
      exact hw.right k (by omega) hkn
    · intro k hk hwrite
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkj|rfl
      · rw [at' _ (by omega),ite_eq_right (by omega)]
        exact hw.done k hkj hwrite
      · rw [at' _ (by omega),ite_eq_left ⟨hwrite,rfl⟩]
    · intro k hk hfr; rw [at' k hk,ite_eq_right (by rcases hfr with h|h|h <;> simp_all <;> omega)]
      exact hw.frame k hk hfr
  obtain ⟨t,run,ht⟩ := Eval.forRange_invariant_exact (body := .seq p.cell shift)
    4 5 n 7 I s hs hi (fun j t h => ⟨h.safe,h.counter,h.size⟩) body
  exact ⟨t,by simpa [scan,Nat.mul_comm] using run,ht.accum,ht.done,ht.frame,ht.indices⟩

end OutputPass
end PrimalDual
end LinearProgramming
end Optimization
end OAI
