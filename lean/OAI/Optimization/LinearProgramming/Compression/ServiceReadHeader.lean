import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Reading a small nonnegative integer previously written to the persistent scalar header.
Only arithmetic, exact comparisons, and address increments are used. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Load the natural in scalar register `src` into address register `dst`. Scalar registers
0 and 6 are scratch. The time is linear in the **value** read; the service uses this routine
only on dimensions and the number of generators, which are dimension-polynomial. -/
def headerToAddress (src dst : ℕ) : Block :=
  .seq (.op (.const 0 0)) (.seq (.op (.const 6 1)) (.seq (.op (.addrConst dst 0))
    (.loop (.scalarLT 0 src) (.seq (.op (.add 0 0 6)) (.op (.incr dst dst))))))

theorem headerToAddress_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (src dst n : ℕ) (hs0 : src≠0) (hs6 : src≠6)
    (hsrc : s.data src=(n : K)) (hs : ∀ i, P (s.data i))
    (h1 : P 1) (hn : ∀ j≤n, P (j : K)) :
    ∃ t, Block.Eval (fun m => ∀ i, P (m.data i)) (headerToAddress src dst) s (4*n+4) t ∧
      t.index dst=n ∧ (∀ i, i≠dst → t.index i=s.index i) ∧
      ∀ i, i≠0 → i≠6 → t.data i=s.data i := by
  let safe := fun m : Memory K => ∀ i, P (m.data i)
  have put {m : Memory K} {d : ℕ} {v : K} (hm : safe m) (hv : P v) : safe (m.putData d v) := by
    intro i
    by_cases h : i=d
    · simpa [h] using hv
    · simpa [h] using hm i
  let a := s.putData 0 ((0 : ℚ) : K)
  let b := a.putData 6 ((1 : ℚ) : K)
  let c := b.putIndex dst 0
  have hzero : P (0:K) := by simpa using hn 0 (Nat.zero_le _)
  have ha : safe a := put hs (by simpa using hzero)
  have hb : safe b := put ha (by simpa using h1)
  have ea : Block.Eval safe (.op (.const 0 0)) s 1 a := by
    exact Block.Eval.op_const (safe := safe) s 0 0 hs ha
  have eb : Block.Eval safe (.op (.const 6 1)) a 1 b := by
    exact Block.Eval.op_const (safe := safe) a 6 1 ha hb
  have ec : Block.Eval safe (.op (.addrConst dst 0)) b 1 c := Block.Eval.op_addrConst _ _ _ hb hb
  let I := fun (j : ℕ) (m : Memory K) =>
    safe m ∧ m.data 0=(j:K) ∧ m.data 6=1 ∧ m.index dst=j ∧
    (∀ i, i≠dst → m.index i=s.index i) ∧ ∀ i, i≠0 → i≠6 → m.data i=s.data i
  have base : I 0 c := by
    refine ⟨hb, by simp [c,b,a], by simp [c,b], by simp [c], ?_, ?_⟩
    · intro i h; simp [c,b,a,h]
    · intro i h₀ h₆; simp [c,b,a,h₀,h₆]
  have one (j : ℕ) (hj : j<n) (m : Memory K) (h : I j m) :
      (Cond.scalarLT 0 src).test m = true ∧ ∃ t,
        Block.Eval safe (.seq (.op (.add 0 0 6)) (.op (.incr dst dst))) m 2 t ∧ I (j+1) t := by
    obtain ⟨hm,h0,h6,hidx,hfi,hfd⟩ := h
    have htest := (hfd src hs0 hs6).trans hsrc
    refine ⟨by simpa [Cond.test,h0,htest] using hj, ?_⟩
    let a := m.putData 0 (m.data 0 + m.data 6)
    let b := a.putIndex dst (a.index dst+1)
    have val : m.data 0 + m.data 6 = (↑(j+1) : K) := by simp [h0,h6]
    have ha : safe a := put hm (val ▸ hn _ hj)
    have ea : Block.Eval safe (.op (.add 0 0 6)) m 1 a := Block.Eval.op_add _ _ _ _ hm ha
    have eb : Block.Eval safe (.op (.incr dst dst)) a 1 b := Block.Eval.op_incr _ _ _ ha ha
    refine ⟨b,ea.seq eb,ha,by simp [b,a,val],by simp [b,a,h6],by simp [b,a,hidx],?_,?_⟩
    · intro i hi; simpa [b,a,hi] using hfi i hi
    · intro i hi hi'; simpa [b,a,hi] using hfd i hi hi'
  have stop (m : Memory K) (h : I n m) : (Cond.scalarLT 0 src).test m = false ∧ safe m := by
    obtain ⟨hm,h0,_,_,_,hfd⟩ := h
    exact ⟨by simp [Cond.test,h0,(hfd src hs0 hs6).trans hsrc],hm⟩
  obtain ⟨t,et,_,_,_,hdst,hfi,hfd⟩ := Block.Eval.loop_invariant_exact I c n 2 base one stop
  refine ⟨t,?_,hdst,hfi,hfd⟩
  unfold headerToAddress
  convert ea.seq (eb.seq (ec.seq et)) using 1
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
