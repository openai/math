import OAI.Optimization.LinearProgramming.Compression.MinorBatchHeader
import OAI.Optimization.LinearProgramming.Compression.Elimination
import OAI.Optimization.LinearProgramming.Compression.UniformBirdCellData
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

/-- Mathematical result for a described selection, including an empty or singular minor. -/
def answerOf {K : Type*} [CommRing K] (v : Layout K) : K := (v.matrix.submatrix v.row v.col).det

/-- The properties of one *fixed* determinant subroutine needed by a repeat caller. -/
def BatchCallSpec (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (call : Block) : Prop :=
  ∀ (v : Layout K) (m : Memory K) (N : ℕ), Input v m → 7 ≤ v.dst →
    v.m ≤ N → v.n ≤ N → v.k ≤ N → ∀ P : K → Prop, (∀ p, P (m.data p)) → P 0 → P 1 →
    (∀ x, P x → P (-x)) → (∀ j<v.k, ∀ r : BirdRegister v.k, P (r.read (v.matrix.submatrix v.row v.col)
      (birdLayer (v.matrix.submatrix v.row v.col) j))) →
    ∃ t c, c ≤ 2200*(N+1)^7 ∧ Block.Eval (fun z => ∀p, P (z.data p)) call m c t ∧
      t.data 6=answerOf v ∧ (∀ p, 7 ≤ p → p < v.dst → t.data p=m.data p) ∧
      ∀ p, 16 ≤ p → t.index p=m.index p

/-- Run the same subroutine from one descriptor and append the result to the answer tape. -/
def batchBody (call : Block) : Block := .seq (loadDescriptor 6 0)
  (.seq call (.seq (.op (.store 18 6)) (.op (.incr 18 18))))

/-- The count and the record and output pointers arrive at runtime in register 16, 17 and 18. -/
def batchBlock (call : Block) : Block := .forRange 19 16 (batchBody call)

private structure BatchState {K : Type} [CommRing K] {q : ℕ} (v : BatchLayout K q) (P : K → Prop)
    (m : Memory K) (c : ℕ) (s : Memory K) : Prop where
  good : ∀ a, P (s.data a)
  count : s.index 16=q
  head : s.index 17=v.headerBase+6*c
  output : s.index 18=v.answerBase+c
  counter : s.index 19=c
  indexFrame : ∀ a, 20≤a → s.index a=m.index a
  scalarFrame : ∀ a, 7≤a → a<v.answerBase → s.data a=m.data a
  answers : ∀ a : Fin q, a.val<c → s.data (v.answerBase+a.val)=answerOf (v.query a)

private theorem batchStep {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (call : Block) (hcall : BatchCallSpec K call) {q : ℕ} (v : BatchLayout K q) (m : Memory K)
    (initial : BatchInput v m) (N : ℕ) (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N)
    (P : K → Prop) (hz : P 0) (ho : P 1) (hneg : ∀ x, P x → P (-x))
    (hreg : ∀a, ∀j<(v.query a).k, ∀r : BirdRegister (v.query a).k,
      P (r.read ((v.query a).matrix.submatrix (v.query a).row (v.query a).col)
        (birdLayer ((v.query a).matrix.submatrix (v.query a).row (v.query a).col) j)))
    (c : ℕ) (hc : c<q) (s : Memory K) (h : BatchState v P m c s) :
    ∃ t cost, cost ≤ 2200*(N+1)^7+14 ∧ Block.Eval (fun z => ∀p, P (z.data p)) (batchBody call) s cost t ∧
      BatchState v P m (c+1) (t.putIndex 19 (t.index 19+1)) := by
  let a : Fin q := ⟨c,hc⟩
  let u := v.query a
  have hhead : 20 ≤ s.index 17 := h.head ▸ v.header_ge.trans (Nat.le_add_right ..)
  obtain ⟨w, hw, wd, whead, wfields, wframe⟩ := loadDescriptor_spec P 6 0 (by decide) s hhead h.good
  have publicIndex (p : ℕ) (hp : 20≤p) : w.index p=m.index p :=
    (wframe p (by omega) (.inr (by omega))).trans (h.indexFrame p hp)
  have field (j : ℕ) (hj : j<6) : w.index j=descriptorWord u j := by
    have eq := wfields j hj
    rw [Nat.zero_add,h.head] at eq
    exact eq.trans ((h.indexFrame _ (by have := v.header_ge; omega)).trans (initial.words a j hj))
  have inp : Input u w := by
    refine ⟨field 0 (by decide), field 1 (by decide), field 2 (by decide), field 3 (by decide),
      field 4 (by decide), field 5 (by decide), ?_, ?_, ?_⟩
    · intro i
      exact (publicIndex _ ((v.row_ge a).trans (Nat.le_add_right ..))).trans (initial.rows a i)
    · intro j
      exact (publicIndex _ ((v.col_ge a).trans (Nat.le_add_right ..))).trans (initial.cols a j)
    · intro i j
      rw [wd]
      have ha := flat_lt i.isLt j.isLt
      have hsrc : 7 ≤ u.src := v.source_ge a
      have hend : u.src+u.m*u.n ≤ v.answerBase := v.source_end a
      exact (h.scalarFrame _ (by omega) (by omega)).trans (initial.source a i j)
  have hdest : 7 ≤ u.dst := v.answer_ge.trans ((Nat.le_add_right ..).trans (v.answers_end a))
  obtain ⟨t, sk, hsk, ht, hres, htdata, htindex⟩ := hcall u w N inp hdest
    (hN a).1 (hN a).2.1 (hN a).2.2 P (wd ▸ h.good) hz ho hneg (hreg a)
  have preserved (p : ℕ) (hp : 7≤p) (hyp : p<u.dst) : t.data p=s.data p := by
    rw [htdata p hp hyp,wd]
  have frame (p : ℕ) (hp : 16≤p) (hh : p≠17) : t.index p=s.index p :=
    (htindex p hp).trans (wframe p hh (.inr (by omega)))
  have addr : t.index 18=v.answerBase+c := (frame 18 (by decide) (by decide)).trans h.output
  let x := t.putData (t.index 18) (t.data 6)
  let y := x.putIndex 18 (x.index 18+1)
  have hx : ∀ p, P (x.data p) := birdScalarPut ht.safe_end _ _ (ht.safe_end 6)
  have store : Block.Eval (fun z => ∀p,P (z.data p)) (.op (.store 18 6)) t 1 x :=
    Block.Eval.op_store _ _ _ ht.safe_end hx
  have incr : Block.Eval (fun z => ∀p,P (z.data p)) (.op (.incr 18 18)) x 1 y :=
    Block.Eval.op_incr _ _ _ hx hx
  refine ⟨y,12+(sk+(1+1)), by omega, hw.seq (ht.seq (store.seq incr)), ?_⟩
  have tcount := (frame 16 (by decide) (by decide)).trans h.count
  have tctr := (frame 19 (by decide) (by decide)).trans h.counter
  have tptr : t.index 17=v.headerBase+6*(c+1) := by
    rw [htindex 17 (by decide),whead,h.head]; omega
  refine ⟨hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [y,x,Memory.putIndex,Memory.putData] using tcount
  · simpa [y,x,Memory.putIndex,Memory.putData] using tptr
  · simp [y,x,Memory.putIndex,Memory.putData,addr,Nat.add_assoc]
  · simp [y,x,Memory.putIndex,Memory.putData,tctr]
  · intro p hp
    have := (frame p (by omega) (by omega)).trans (h.indexFrame p hp)
    simpa [y,x,Memory.putIndex,Memory.putData, Function.update_of_ne (by omega : p≠19),
      Function.update_of_ne (by omega : p≠18)] using this
  · intro p hp hlo
    have end' := v.answers_end a
    change (Function.update t.data (t.index 18) (t.data 6)) p=m.data p
    rw [addr, Function.update_of_ne (by omega : p≠v.answerBase+c), preserved p hp (by dsimp [u]; omega)]
    exact h.scalarFrame p hp hlo
  · intro b hb
    change (Function.update t.data (t.index 18) (t.data 6)) (v.answerBase+b.val)=_
    rw [addr]
    by_cases heq : b.val=c
    · have he : b=a := Fin.ext heq
      subst b; exact (Function.update_self ..).trans hres
    · have hb' : b.val<c := by omega
      have hb0 : 7 ≤ v.answerBase+b.val := v.answer_ge.trans (Nat.le_add_right ..)
      have hb1 : v.answerBase+b.val<u.dst := (Nat.add_lt_add_left b.isLt _).trans_le (v.answers_end a)
      rw [Function.update_of_ne (by omega : v.answerBase+b.val≠v.answerBase+c), preserved _ hb0 hb1]
      exact h.answers b hb'

/-- Arbitrary many requests use one fixed body. Original inputs, the runtime descriptors and
previous answers survive later calls, and each intermediate scalar satisfies the same bound. -/
theorem batchBlock_eval_cursors {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (call : Block) (hcall : BatchCallSpec K call) {q : ℕ} (v : BatchLayout K q) (m : Memory K)
    (initial : BatchInput v m) (N : ℕ) (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N)
    (P : K → Prop) (initialP : ∀ p, P (m.data p)) (hz : P 0) (ho : P 1) (hneg : ∀ x, P x → P (-x))
    (hreg : ∀a, ∀j<(v.query a).k, ∀r : BirdRegister (v.query a).k,
      P (r.read ((v.query a).matrix.submatrix (v.query a).row (v.query a).col)
        (birdLayer ((v.query a).matrix.submatrix (v.query a).row (v.query a).col) j))) :
    ∃ t cost, cost ≤ q*(2200*(N+1)^7+17)+2 ∧ Block.Eval (fun z => ∀p, P (z.data p)) (batchBlock call) m cost t ∧
      (∀ a : Fin q, t.data (v.answerBase+a.val)=answerOf (v.query a)) ∧
      (∀ a, 7≤a → a<v.answerBase → t.data a=m.data a) ∧ (∀ a, 20≤a → t.index a=m.index a) ∧
      t.index 16 = q ∧ t.index 17 = v.headerBase+6*q ∧ t.index 18 = v.answerBase+q := by
  have start : BatchState v P m 0 (m.putIndex 19 0) := by
    refine ⟨initialP, initial.count, ?_, ?_, by simp [Memory.putIndex], ?_, fun _ _ _ => rfl, ?_⟩
    · simpa [Memory.putIndex] using initial.header
    · simpa [Memory.putIndex] using initial.answer
    · intro a ha; simp [Memory.putIndex, Function.update_of_ne (by omega : a≠19)]
    · intro a ha; omega
  obtain ⟨t, c, hc, hr, h⟩ := Block.Eval.forRange_invariant (body := batchBody call) 19 16 q
    (2200*(N+1)^7+14) (BatchState v P m) m initialP start
    (fun _ _ x => ⟨x.good,x.counter,x.count⟩) (batchStep call hcall v m initial N hN P hz ho hneg hreg)
  exact ⟨t,c,by omega,hr,(fun a => h.answers a a.isLt),h.scalarFrame,h.indexFrame,h.count,h.head,h.output⟩

/-- The batch result when the caller only needs the answer tape and preserved inputs. -/
theorem batchBlock_eval {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (call : Block) (hcall : BatchCallSpec K call) {q : ℕ} (v : BatchLayout K q) (m : Memory K)
    (initial : BatchInput v m) (N : ℕ) (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N)
    (P : K → Prop) (initialP : ∀ p, P (m.data p)) (hz : P 0) (ho : P 1) (hneg : ∀ x, P x → P (-x))
    (hreg : ∀a, ∀j<(v.query a).k, ∀r : BirdRegister (v.query a).k,
      P (r.read ((v.query a).matrix.submatrix (v.query a).row (v.query a).col)
        (birdLayer ((v.query a).matrix.submatrix (v.query a).row (v.query a).col) j))) :
    ∃ t cost, cost ≤ q*(2200*(N+1)^7+17)+2 ∧ Block.Eval (fun z => ∀p, P (z.data p)) (batchBlock call) m cost t ∧
      (∀ a : Fin q, t.data (v.answerBase+a.val)=answerOf (v.query a)) ∧
      (∀ a, 7≤a → a<v.answerBase → t.data a=m.data a) ∧ ∀ a, 20≤a → t.index a=m.index a := by
  obtain ⟨t,c,hc,ev,ans,scalars,indices,_⟩ :=
    batchBlock_eval_cursors call hcall v m initial N hN P initialP hz ho hneg hreg
  exact ⟨t,c,hc,ev,ans,scalars,indices⟩

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
