import OAI.Optimization.LinearProgramming.RAM.CallableBootScalarStage
import OAI.Optimization.LinearProgramming.RAM.ArrayFill

/-! Scatter staged scalars to the odd bank, then erase the high buffer and the
even slots. Every scalar written is an input value or zero. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

private def oddOps : List AddressOp := [.copy 3 7,.set 4 1]
private def clearOps : List AddressOp := [.copy 3 0,.set 4 2,.decr 6 2]
def scalarBlock : Block := .seq scalarStage <| .seq (program oddOps) <| .seq (copyData 2 1 2) <|
  .seq (.op (.const 0 0)) <| .seq (RAM.fillBlock 0 7 3 5 2) <|
  .seq (program clearOps) <| .seq (copyData 6 0 2) (.op (.const 0 0))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem scalarBlock_spec (P : K→Prop) (s : Memory K) (cap n : ℕ)
    (hs : s.AllData P) (hP0 : P 0) (h0 : s.index 0=cap) (h2 : s.index 2=n)
    (room : 2*n+4 ≤ cap) (zero : ∀r, n ≤ r → s.data r=0) :
    ∃ t k, k ≤ 40*(n+1) ∧ Eval (Memory.AllData P) scalarBlock s k t ∧
      (∀ r, t.data r=if r%2=1 then s.data (r/2) else 0) ∧
      ∀ r, r < 3 ∨ 7 < r → t.index r=s.index r := by
  obtain ⟨m,stage,m7,staged,mzero,mi⟩ := scalarStage_spec P s cap n hs h0 h2 room zero
  let a := applyOps oddOps m
  have ea := ops_spec P oddOps m stage.safe_end
  have alen : a.index 2=n := by
    simpa [a,oddOps,applyOps,AddressOp.apply] using (mi 2 (by decide)).trans h2
  obtain ⟨u,eu,uw,uf,ui⟩ := copyData_spec P a 2 1 2 n (cap+1) 1 ea.safe_end
    (.inl rfl) alen (by simp [a,oddOps,applyOps,AddressOp.apply,m7])
    (by simp [a,oddOps,applyOps,AddressOp.apply]) (by omega) (by decide) (by decide)
    (.inr (by omega))
  have u7 : u.index 7=cap+1 := by
    simpa [a,oddOps,applyOps,AddressOp.apply,m7] using ui 7 (by decide) (by decide) (by decide)
  have u2 : u.index 2=n := (ui 2 (by decide) (by decide) (by decide)).trans alen
  let v := u.putData 0 0
  have sv : v.AllData P := eu.safe_end.putData _ hP0
  have ev : Eval (Memory.AllData P) (.op (.const 0 0)) u 1 v := by
    simpa [v] using Eval.op_const (safe:=Memory.AllData P) u 0 0 eu.safe_end (by simpa using sv)
  obtain ⟨z,ez,zw,zf,_,_,zi⟩ := RAM.fillBlock_correct P v 0 7 3 5 2 n (by decide)
    (by decide) (by decide) u2 (by change 0 < u.index 7; omega) sv
  have zodd (i : ℕ) (hi : i < n) : z.data (2*i+1)=s.data i := by
    have frame := zf (2*i+1) (.inl (by change 2*i+1 < u.index 7; omega))
    have written := uw i hi
    have val := staged i hi
    simp only [Nat.one_mul,show 1+2*i=2*i+1 by omega] at written
    exact frame.trans ((Memory.putData_ne u (by omega) _).trans (written.trans val))
  have ztail (r : ℕ) (hr : 2*n ≤ r) : z.data r=0 := by
    by_cases window : cap+1 ≤ r ∧ r < cap+1+n
    · have hit := zw (r-(cap+1)) (by omega)
      simpa [v,u7,show cap+1+(r-(cap+1))=r by omega] using hit
    · have eq := zf r (by change r < u.index 7 ∨ u.index 7+n ≤ r; omega)
      by_cases r0 : r=0
      · simpa [r0,v] using eq
      · have prior := uf r r0 (fun i hi => by omega)
        exact eq.trans ((Memory.putData_ne u r0 _).trans (prior.trans
          ((congrFun (ops_data oddOps m) r).trans (mzero r r0 (by omega) (by omega)))))
  have iz (r : ℕ) (hr : r < 3 ∨ 7 < r) : z.index r=s.index r := by
    have z' := zi r (by omega) (by omega)
    have u' := ui r (by omega) (by omega) (by omega)
    have a' : a.index r=m.index r := by simp (disch := omega) [a,oddOps,applyOps,AddressOp.apply]
    exact z'.trans (u'.trans (a'.trans (mi r hr)))
  let q := applyOps clearOps z
  have eq := ops_spec P clearOps z ez.safe_end
  have z0 := (iz 0 (by decide)).trans h0
  have z2 := (iz 2 (by decide)).trans h2
  obtain ⟨y,ey,yw,yf,yi⟩ := copyData_spec P q 6 0 2 (n-1) cap 2 eq.safe_end
    (.inr rfl) (by simp [q,clearOps,applyOps,AddressOp.apply,z2])
    (by simp [q,clearOps,applyOps,AddressOp.apply,z0])
    (by simp [q,clearOps,applyOps,AddressOp.apply]) (by omega) (by decide) (by decide)
    (.inr (by omega))
  let t := y.putData 0 0
  have et : Eval (Memory.AllData P) (.op (.const 0 0)) y 1 t := by
    simpa [t] using Eval.op_const (safe:=Memory.AllData P) y 0 0 ey.safe_end
      (by simpa using ey.safe_end.putData 0 hP0)
  have yd (r : ℕ) (h : r≠0) (miss : ∀ i < n-1, r≠2+2*i) : t.data r=z.data r :=
    (Memory.putData_ne y h _).trans ((yf r h miss).trans (congrFun (ops_data clearOps z) r))
  have whole := stage.seq (ea.seq (eu.seq (ev.seq (ez.seq (eq.seq (ey.seq et))))))
  refine ⟨t,_,?_,whole,?_,?_⟩
  · change 4+(1+((n-1)*7+2))+(2+(n*8+2+(1+(5*n+3+(3+((n-1)*7+2+1)))))) ≤ 40*(n+1)
    omega
  · intro r
    by_cases parity : r%2=1
    · simp [parity]
      rw [yd r (by omega) (fun j hj => by omega)]
      by_cases inside : r/2 < n
      · simpa only [show 2*(r/2)+1=r by omega] using zodd (r/2) inside
      · rw [ztail r (by omega),zero _ (by omega)]
    · simp [parity]
      by_cases at0 : r=0
      · simp [t,at0]
      · by_cases inside : r/2 < n
        · have val := yw (r/2-1) (by omega)
          have zc := ztail cap (by omega)
          simp only [Nat.zero_mul,Nat.add_zero,show 2+2*(r/2-1)=r by omega] at val
          exact (Memory.putData_ne y at0 _).trans (val.trans ((congrFun (ops_data clearOps z) cap).trans zc))
        · exact (yd r at0 (fun j hj => by omega)).trans (ztail r (by omega))
  · intro r hr
    have hf := yi r (by omega) (by omega) (by omega)
    have fq : q.index r=z.index r := by simp (disch := omega) [q,clearOps,applyOps,AddressOp.apply]
    exact hf.trans (fq.trans (iz r hr))

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
