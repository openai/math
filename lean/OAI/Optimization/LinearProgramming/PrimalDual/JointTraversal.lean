import OAI.Optimization.LinearProgramming.PrimalDual.JointCell
import OAI.Optimization.LinearProgramming.PrimalDual.Layout
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Sequential emission of every matrix and right-hand-side word of the second feasibility call. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace JointRAM

open RAM RAM.Block RAM.Tape Polynomial

/-- A source LP with its objective and the locations of two scalar tape windows. -/
structure Layout (K : Type*) where
  m : Nat
  d : Nat
  matrix : Matrix (Fin m) (Fin d) K
  rhs : Fin m → K
  objective : Fin d → K
  src : Nat
  dst : Nat

namespace Layout

variable {K : Type*}

def rows (b : Layout K) := b.m+(b.m+(b.d+(b.d+1)))
def cols (b : Layout K) := b.d+b.m
def inputLength (b : Layout K) := b.m*b.d+b.m+b.d

def sourceWord [Zero K] (b : Layout K) := optInputWord b.matrix b.rhs b.objective

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def destination (b : Layout K) : List K :=
  lpInput (finJointMatrix b.matrix b.rhs b.objective) (finJointRhs b.rhs b.objective)

def word (b : Layout K) (i : Nat) : K := (b.destination[i]?).getD 0

def offset (b : Layout K) (r j : Nat) : Nat := if j < b.cols then r*b.cols+j else b.rows*b.cols+r

private theorem read_word (b : Layout K) {r j : Nat} (hr : r < b.rows) (hj : j ≤ b.cols) :
    (jointDatum b.m b.d r j).read b.sourceWord = b.word (b.offset r j) := by
  by_cases h : j < b.cols
  · have hm := jointDatum_matrix b.matrix b.rhs b.objective ⟨r,hr⟩ ⟨j,h⟩
    have hw := lpInput_matrix_word (finJointMatrix b.matrix b.rhs b.objective)
      (finJointRhs b.rhs b.objective) ⟨r,hr⟩ ⟨j,h⟩
    change _[r*b.cols+j]? = _ at hw
    simpa [word,destination,offset,h,hw,sourceWord] using hm
  · have heq : j = b.cols := by omega
    subst j
    have hm := jointDatum_rhs b.matrix b.rhs b.objective ⟨r,hr⟩
    have hw := lpInput_rhs_word (finJointMatrix b.matrix b.rhs b.objective)
      (finJointRhs b.rhs b.objective) ⟨r,hr⟩
    change _[b.rows*b.cols+r]? = _ at hw
    apply hm.trans
    change _ = (b.destination[b.offset r b.cols]?).getD 0
    rw [show b.offset r b.cols = b.rows*b.cols+r by simp [offset]]
    change _ = (lpInput (finJointMatrix b.matrix b.rhs b.objective)
      (finJointRhs b.rhs b.objective))[b.rows*b.cols+r]?.getD 0
    simp only [hw, Option.getD_some]

/-- Exact source and produced prefix, plus the fixed headers needed by each visit. -/
structure Written (b : Layout K) (P : K → Prop) (q : Nat) (s : Memory K) (original : Nat → K) : Prop where
  safe : Good P s
  zeroData : s.data 1 = 0
  mReg : s.index 0 = b.m
  dReg : s.index 1 = b.d
  srcReg : s.index 2 = b.src
  dstReg : s.index 3 = b.dst
  rowsReg : s.index 6 = b.rows
  colsReg : s.index 7 = b.cols
  cursor : s.index 8 = b.dst+q
  input : ∀ k < b.inputLength, s.data (b.src+k) = b.sourceWord k
  output : ∀ i < q, s.data (b.dst+i) = b.word i
  outside : ∀ i, 1 < i → (i < b.dst ∨ b.dst+q ≤ i) → s.data i = original i

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem Written.putCounter {b : Layout K} {P : K → Prop} {q : Nat} {s : Memory K}
    {original : Nat → K} (h : Written b P q s original) {c : Nat} (hc : c=4 ∨ c=5) (v : Nat) : Written b P q (s.putIndex c v) original := by
  rcases hc with rfl | rfl <;>
    exact ⟨h.safe,h.zeroData,by simpa [Memory.putIndex] using h.mReg,
      by simpa [Memory.putIndex] using h.dReg, by simpa [Memory.putIndex] using h.srcReg,
      by simpa [Memory.putIndex] using h.dstReg,by simpa [Memory.putIndex] using h.rowsReg,
      by simpa [Memory.putIndex] using h.colsReg,by simpa [Memory.putIndex] using h.cursor,
      h.input,h.output,h.outside⟩

/-- A uniform bound on every coefficient probe in one dense output tape. -/
def BoundedEntries (b : Layout K) (B : Nat) : Prop := ∀ e : Env,
  e 0 = b.m → e 1 = b.d → e 4 < b.rows → e 5 ≤ b.cols → entry.cost e 2+2 ≤ B

private theorem Written.emit {b : Layout K} {B : Nat} (budget : b.BoundedEntries B) {P : K → Prop} {q r j : Nat} {s : Memory K}
    {original : Nat → K} (w : Written b P q s original) (h0 : P 0) (h1 : P (-1)) (hneg : ∀ x, P x → P (-x))
    (srcSafe : 2 ≤ b.src) (separate : b.src+b.inputLength ≤ b.dst)
    (hr : r < b.rows) (hj : j ≤ b.cols) (hrow : s.index 4 = r) (hcol : s.index 5 = j)
    (hq : q = b.offset r j) :
    ∃ t k, k ≤ B ∧ Eval (Good P) JointRAM.emit s k t ∧
      Written b P (q+1) t original ∧ t.index 4 = r ∧ t.index 5 = j := by
  have hr' : r < 2*b.m+2*b.d+1 := by unfold rows at hr; omega
  obtain ⟨k,t,he,hk,hd,hi,hcur,hval⟩ := emit_correct s w.safe h0 h1 hneg w.zeroData
  have hcost := budget (fun i : Fin 9 => s.index i) w.mReg w.dReg
    (hrow.trans_lt hr) (hcol.trans_le hj)
  have hout : t.data (b.dst + q) = b.word q := by
    rw [w.cursor,w.mReg,w.dReg,w.srcReg,hrow,hcol] at hval
    rw [hval,hq,b.read_word hr hj |>.symm]
    cases eq : jointDatum b.m b.d r j with
    | zero | negOne => rfl
    | source idx neg =>
      have hidx := source_in_bounds hr' hj eq
      have rs := w.input idx hidx
      cases neg <;> simp [JointDatum.read,rs]
  have fro (i : Nat) (h : i < 8) : t.index i = s.index i := hi i (by omega) (by omega)
  refine ⟨t,k,?_,he,?_,(fro 4 (by decide)).trans hrow,(fro 5 (by decide)).trans hcol⟩
  · exact hk.trans hcost
  refine ⟨he.safe_end, (hd 1 (by decide) (by rw [w.cursor]; omega)).trans w.zeroData,
    (fro 0 (by decide)).trans w.mReg,(fro 1 (by decide)).trans w.dReg,
    (fro 2 (by decide)).trans w.srcReg,(fro 3 (by decide)).trans w.dstReg,
    (fro 6 (by decide)).trans w.rowsReg,(fro 7 (by decide)).trans w.colsReg,
    by rw [hcur,w.cursor]; omega, ?_, ?_, ?_⟩
  · intro i hlen
    exact (hd (b.src+i) (by omega) (by rw [w.cursor]; omega)).trans (w.input i hlen)
  · intro i hiq
    by_cases hiq' : i=q
    · simpa [hiq'] using hout
    · exact (hd (b.dst+i) (by omega) (by rw [w.cursor]; omega)).trans (w.output i (by omega))

  · intro i hi hregion
    apply (hd i (by omega) (by rw [w.cursor]; rcases hregion with h|h <;> omega)).trans
    exact w.outside i hi (by rcases hregion with h|h <;> omega)

end Layout

/-- The two loops write the entire rectangular coefficient array in row-major order,
followed by the RHS vector. The second traversal fixes the column to the RHS sentinel. -/
def traverse : Block := .seq (.forRowsCols 4 6 5 7 emit)
  (.seq (.op (.addrCopy 5 7)) (.forRange 4 6 emit))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem traverse_correct (b : Layout K) (B : Nat) (budget : b.BoundedEntries B) (P : K → Prop) (h0 : P 0) (h1 : P (-1))
    (hneg : ∀ x, P x → P (-x)) (srcSafe : 2 ≤ b.src) (separate : b.src+b.inputLength ≤ b.dst)
    (s : Memory K) {original : Nat → K} (hw : b.Written P 0 s original) :
    ∃ t k, k ≤ (b.rows*(b.cols*(B+3)+5)+2)+(1+(b.rows*(B+3)+2)) ∧
      Eval (Good P) traverse s k t ∧ b.Written P (b.rows*b.cols+b.rows) t original := by
  let R := fun r (t : Memory K) => b.Written P (r*b.cols) t original ∧ t.index 4 = r
  let C := fun r j (t : Memory K) => b.Written P (r*b.cols+j) t original ∧ t.index 4 = r ∧ t.index 5 = j
  have initial : R 0 (s.putIndex 4 0) := ⟨by simpa using hw.putCounter (Or.inl rfl) 0, getPutSame _ _ _⟩
  obtain ⟨z,k,hk,he,w,hrow⟩ := Eval.forRowsCols_invariant (safe := Good P) (body := emit)
    4 6 5 7 b.rows b.cols B R C s hw.safe initial
    (fun _ _ h => ⟨h.1.safe,h.2,h.1.rowsReg⟩)
    (fun r _ t h => ⟨by simpa using h.1.putCounter (Or.inr rfl) 0,
      (getPutDifferent _ (by decide : (4:Nat) ≠ 5)).trans h.2,getPutSame _ _ _⟩)
    (fun _ _ _ h => ⟨h.1.safe,h.2.2,h.1.colsReg⟩)
    (by
      intro r hr j hj t h
      obtain ⟨u,l,hl,he,hw,ha,hj'⟩ := h.1.emit budget h0 h1 hneg srcSafe separate hr hj.le h.2.1 h.2.2
        (by simp [Layout.offset,hj])
      refine ⟨u,l,hl,he,?_,(getPutDifferent _ (by decide : (4:Nat) ≠ 5)).trans ha,?_⟩
      · exact hw.putCounter (Or.inr rfl) _
      · simp [hj'])
    (by
      intro r _ t h
      refine ⟨?_, ?_⟩
      · simpa only [Nat.add_mul,one_mul] using h.1.putCounter (Or.inl rfl) (t.index 4+1)
      · simp [h.2.1])
  let z' := z.putIndex 5 (z.index 7)
  have w' := w.putCounter (Or.inr rfl) (z.index 7)
  let S := fun r (t : Memory K) => b.Written P (b.rows*b.cols+r) t original ∧ t.index 4=r ∧ t.index 5=b.cols
  have initR : S 0 (z'.putIndex 4 0) := by
    refine ⟨by simpa using w'.putCounter (Or.inl rfl) 0, getPutSame _ _ _, ?_⟩
    simp [z',w.colsReg]
  obtain ⟨t,l,hl,run,hr,_,_⟩ := Eval.forRange_invariant (safe := Good P) (body := emit)
    4 6 b.rows B S z' w.safe initR (fun _ _ h => ⟨h.1.safe,h.2.1,h.1.rowsReg⟩) (by
      intro r hra t h
      obtain ⟨u,j,hj,he,hn,hr',hc'⟩ := h.1.emit budget h0 h1 hneg srcSafe separate hra le_rfl h.2.1 h.2.2
        (by simp [Layout.offset])
      refine ⟨u,j,hj,he,hn.putCounter (Or.inl rfl) _,?_,?_⟩
      · simp [hr']
      · simpa using hc')
  exact ⟨t,_,Nat.add_le_add hk (Nat.add_le_add_left hl 1),
    .seq he (.seq (eval_copyI z w.safe 5 7) run),hr⟩

end JointRAM
end PrimalDual
end LinearProgramming
end Optimization
end OAI
