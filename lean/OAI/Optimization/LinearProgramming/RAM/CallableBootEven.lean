import OAI.Optimization.LinearProgramming.RAM.CallableBootOps

/-! Clear the even address slots above the fixed control registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

private def evenSetup : List AddressOp := [.set 3 12,.incr 4 0,.set 5 0]
private def evenOps : List AddressOp := [.store 3 5,.incr 3 3,.incr 3 3]
def clearEvenBlock : Block := .seq (program evenSetup) (.loop (.addrLT 3 4) (program evenOps))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem clearEvenBlock_spec (P : K→Prop) (s : Memory K) (cap : ℕ) (hs : s.AllData P)
    (hc : 64 ≤ cap) (h0 : s.index 0=cap) :
    ∃ t, Eval (Memory.AllData P) clearEvenBlock s (3+((cap/2+1-6)*5+1)) t ∧
      t.data=s.data ∧ t.index 0=cap ∧
      (∀ j, 6 ≤ j → 2*j ≤ cap → t.index (2*j)=0) ∧
      ∀ r, 11 < r → (cap < r ∨ r%2=1) → t.index r=s.index r := by
  let a := applyOps evenSetup s
  let I := fun i (u : Memory K) => u.AllData P ∧ u.data=s.data ∧ u.index 0=cap ∧
    u.index 3=2*(6+i) ∧ u.index 4=cap+1 ∧ u.index 5=0 ∧
    (∀ j, 6 ≤ j → j < 6+i → u.index (2*j)=0) ∧
    ∀ r, 11 < r → (cap < r ∨ r%2=1) → u.index r=s.index r
  have ea := ops_spec P evenSetup s hs
  have hi : I 0 a := by
    refine ⟨ea.safe_end,ops_data ..,?_,?_,?_,?_,fun j hj hj' => (by omega),?_⟩
    all_goals try (intro r hr _)
    all_goals simp (disch := omega) [a,evenSetup,applyOps,AddressOp.apply,h0]
  obtain ⟨t,run,safe,dat,capReg,_,_,_,wr,fr⟩ := Eval.loop_invariant_exact
    (safe:=Memory.AllData P) (c:=.addrLT 3 4) (body:=program evenOps) I a (cap/2+1-6) 3 hi
    (by
      intro i hi u huv
      obtain ⟨safe,dat,capReg,p3,p4,p5,wr,fr⟩ := huv
      have room : 2*(6+i) ≤ cap := by omega
      have test : (Cond.addrLT 3 4).test u=true := by
        simp only [Cond.test,decide_eq_true_eq,p3,p4]
        exact Nat.lt_succ_of_le room
      let v := applyOps evenOps u
      have step := ops_spec P evenOps u safe
      have eq (r : ℕ) (h3 : r≠3) (hl : r≠2*(6+i)) : v.index r=u.index r := by
        simp (disch := omega) [v,evenOps,applyOps,AddressOp.apply,p3,p5]
      refine ⟨test,v,step,step.safe_end,(ops_data ..).trans dat,(eq 0 (by decide) (by omega)).trans capReg,
        ?_,(eq 4 (by decide) (by omega)).trans p4,(eq 5 (by decide) (by omega)).trans p5,?_,?_⟩
      · simp (disch := omega) [v,evenOps,applyOps,AddressOp.apply,p3,p5]
        omega
      · intro j hj hlt
        by_cases e : j=6+i
        · subst j
          simp (disch := omega) [v,evenOps,applyOps,AddressOp.apply,p3,p5]
        · exact (eq _ (by omega) (by omega)).trans (wr j hj (by omega))
      · intro r hr cond
        exact (eq r (by omega) (by omega)).trans (fr r hr cond))
    (by
      intro u h
      obtain ⟨safe,_,_,p3,p4,_⟩ := h
      refine ⟨?_,safe⟩
      simp only [Cond.test,decide_eq_false_iff_not,p3,p4]
      omega)
  exact ⟨t,ea.seq run,dat,capReg,fun j hj room => wr j hj (by omega),fr⟩

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
