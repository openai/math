import OAI.Optimization.LinearProgramming.Recovery.PairBuilderExport

/-! Publish the contiguous two-basis normal input and retain the live LP data. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Call RAM.Callable RAM.Tape Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

variable {K : Type}
variable {h n k s : ℕ} {l : Layout h n} {m t : Memory K}

def PackedTapes (rev : Bool) (l : Layout h n) (F : Matrix (Fin k) (Fin n) K) (R : Matrix (Fin s) (Fin n) K) (t : Memory K) : Prop :=
  if rev then RawTapes t l.out 208 (capacity h n l.previous) (encodedGramInput R++encodedGramInput F) [s,k]
  else RawTapes t l.out 208 (capacity h n l.previous) (encodedGramInput F++encodedGramInput R) [k,s]

structure Prepared [Field K] [LinearOrder K] [IsStrictOrderedRing K] (rev : Bool) (l : Layout h n) (C : Matrix (Fin h) (Fin n) K)
    (F : Matrix (Fin k) (Fin n) K) (R : Matrix (Fin s) (Fin n) K) (t : Memory K) : Prop where
  total : s+k=n
  firstSpan : PacksRows C F
  kernelSpan : PacksRows (kernelRows F) R
  firstTable : uniformRect k n (firstDst rev l.out n k) t=F
  lastTable : uniformRect s n (secondDst rev l.out n k) t=R
  tapes : PackedTapes rev l F R t

/-- The visible rank words are the same ones used in the dense geometric input tape. -/
theorem Prepared.dimensions [Field K] [LinearOrder K] [IsStrictOrderedRing K] {rev : Bool} {C : Matrix (Fin h) (Fin n) K} {F : Matrix (Fin k) (Fin n) K}
    {R : Matrix (Fin s) (Fin n) K} (q : Prepared rev l C F R t) :
    t.index 208=(if rev then s else k) ∧ t.index 209=(if rev then k else s) := by
  cases rev
  · have raw : RawTapes t l.out 208 (capacity h n l.previous) (encodedGramInput F++encodedGramInput R) [k,s] := q.tapes
    exact ⟨raw.addressAt 0 (by decide : 0 < 2), raw.addressAt 1 (by decide : 1 < 2)⟩
  · have raw : RawTapes t l.out 208 (capacity h n l.previous) (encodedGramInput R++encodedGramInput F) [s,k] := q.tapes
    exact ⟨raw.addressAt 0 (by decide : 0 < 2), raw.addressAt 1 (by decide : 1 < 2)⟩

theorem first_second_disjoint (rev : Bool) {out : ℕ} (dim : s+k=n) :
    firstDst rev out n k+k*n ≤ secondDst rev out n k ∨ secondDst rev out n k+s*n ≤ firstDst rev out n k := by
  have hk : n-k=s := by omega
  cases rev <;> simp [firstDst,secondDst,hk]

theorem SourceFrame.trans {u v w : Memory K} (uv : SourceFrame l u v) (vw : SourceFrame l v w) : SourceFrame l u w :=
  ⟨fun j hj=>(vw.1 j hj).trans (uv.1 j hj),fun j h h₁ h₂=>(vw.2 j h h₁ h₂).trans (uv.2 j h h₁ h₂)⟩

/-- All previously allocated LP inputs below the two fresh output regions survive. -/
theorem SourceFrame.below (q : SourceFrame l m t) (i : ℕ) (lo : 5 ≤ i) (hi : i<l.out) : t.data i=m.data i := by
  have work:=l.outputRoom
  exact q.2 i (by omega) (Or.inl hi) (Or.inl (by omega))

theorem SourceFrame.below_rect (q : SourceFrame l m t) {base rows cols : ℕ} (low : 5 ≤ base) (high : base+rows*cols ≤ l.out) :
    uniformRect rows cols base t=uniformRect rows cols base m := by
  ext i j; apply q.below; · omega
  have idx:=rectOffset_lt i j; omega

theorem Passive.source (q : Passive m t) : SourceFrame l m t := ⟨q.held,fun j _ _ _=>congrFun q.data j⟩

theorem Copied.output {p len : ℕ} (q : Copied m t p len) (lo : l.out ≤ p) (hi : p+len ≤ l.out+n*n) : SourceFrame l m t :=
  ⟨q.held,fun j hj aw _=>q.data j hj (by rcases aw with ha|ha <;> omega)⟩

theorem Copied.workspace (q : Copied m t l.scratch (n*n)) : SourceFrame l m t := ⟨q.held,fun j hj _ away=>q.data j hj away⟩

theorem raw_pair {i j : ℕ} (A : Matrix (Fin i) (Fin n) K) (B : Matrix (Fin j) (Fin n) K) (out cap : ℕ)
    (dims : i+j=n) (m : Memory K) (ta : uniformRect i n out m=A) (tb : uniformRect j n (out+i*n) m=B)
    (b : m.index 55=out) (ln : m.index 56=n*n) (d : m.index 57=208) (dl : m.index 58=2) (c : m.index 60=cap)
    (first : m.index 208=i) (last : m.index 209=j) : RawTapes m out 208 cap (encodedGramInput A++encodedGramInput B) [i,j] := by
  refine ⟨b,?_,d,dl,c,?_,?_⟩
  · simpa only [List.length_append,length_encodedGramInput,←Nat.add_mul,dims] using ln
  · intro u hu
    by_cases left : u<(encodedGramInput A).length
    · rw [List.getElem_append_left left]; exact dense_encoded m A ta u left
    · have base : (encodedGramInput A).length ≤ u := by omega
      rw [List.getElem_append_right base]
      simp only [List.length_append,length_encodedGramInput] at hu base ⊢
      have valid : u-i*n<(encodedGramInput B).length := by rw [length_encodedGramInput]; omega
      have tailEntry := dense_encoded m B tb (u-i*n) valid
      have idx : out+i*n+(u-i*n)=out+u := by omega
      simpa only [idx] using tailEntry
  · intro u hu
    rcases u with _|u
    · exact first
    · rcases u with _|u
      · exact last
      · simp at hu

theorem finish [Field K] [LinearOrder K] [IsStrictOrderedRing K] (rev : Bool) (native caller : Memory K) (P : K→Prop) (v : Internal l k s (firstDst rev l.out n k) (secondDst rev l.out n k) caller)
    (hn : native.AllData P) (hc : caller.AllData P) (F : Matrix (Fin k) (Fin n) K) (R : Matrix (Fin s) (Fin n) K)
    (first : uniformRect k n (firstDst rev l.out n k) caller=F) (last : uniformRect s n (secondDst rev l.out n k) caller=R) (dim : s+k=n) :
    ∃t,(«meta» (.finish rev)).Run P (Odd.memory native caller) (metaBudget.eval (limit l)) (Odd.memory native t) ∧
      t.AllData P ∧ Passive caller t ∧ PackedTapes rev l F R t := by
  obtain ⟨t,run,safe,q⟩:=v.metaRun (.finish rev) native P hn hc
  have hv (i : Fin 220) := q.updated i
  have b0 : t.index 55=l.out := by cases rev <;> simpa [plan,HeaderPlan.output,AddressTerm.value,v.target] using hv 55
  have b1 : t.index 56=n*n := by cases rev <;> simpa [plan,HeaderPlan.output,AddressTerm.value,AddressOp.value,v.width] using hv 56
  have b2 : t.index 57=208 := by cases rev <;> simpa [plan,HeaderPlan.output,AddressTerm.value] using hv 57
  have b3 : t.index 58=2 := by cases rev <;> simpa [plan,HeaderPlan.output,AddressTerm.value] using hv 58
  have b4 : t.index 60=capacity h n l.previous := by cases rev <;> simpa [plan,HeaderPlan.output,AddressTerm.value,v.cap] using hv 60
  have m1 := (matrix_frame q.data).trans first; have m2 := (matrix_frame q.data).trans last
  refine ⟨t,run,safe,q.passive,?_⟩
  have hk : n-k=s := by omega
  cases rev
  · apply raw_pair F R l.out _ (by omega) t m1 m2 b0 b1 b2 b3 b4
    · simpa [plan,HeaderPlan.output,AddressTerm.value,v.firstRank] using hv 208
    · simpa [plan,HeaderPlan.output,AddressTerm.value,v.lastRank] using hv 209
  · have m1' : uniformRect k n (l.out+s*n) t=F := by simpa [firstDst,hk] using m1
    apply raw_pair R F l.out _ dim t m2 m1' b0 b1 b2 b3 b4
    · simpa [plan,HeaderPlan.output,AddressTerm.value,v.lastRank] using hv 208
    · simpa [plan,HeaderPlan.output,AddressTerm.value,v.firstRank] using hv 209

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
