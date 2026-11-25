import OAI.Optimization.LinearProgramming.RAM.CallableBootOps

/-! Copy the staged odd words into the physical bank and erase each staging cell
in the same iteration. The lowest six words are retained for the final restoration. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

private def initOps : List AddressOp :=
  [.incr 3 0,.incr 3 3,.incr 3 3,.incr 3 3,.incr 3 3,.incr 3 3,.incr 3 3,
    .set 4 13,.set 5 0,.incr 6 0]
private def moveOps : List AddressOp :=
  [.load 7 3,.store 4 7,.store 3 5,.incr 3 3,.incr 4 4,.incr 4 4]
def scatterBlock : Block := .seq (program initOps) (.loop (.addrLT 4 6) (program moveOps))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private structure DidMove (s t : Memory K) (cap i val : ℕ) : Prop where
  data : t.data=s.data
  odd : t.index (2*i+1)=val
  high : t.index (cap+1+i)=0
  p3 : t.index 3=cap+1+(i+1)
  p4 : t.index 4=2*(i+1)+1
  frame : ∀ r, r≠3 → r≠4 → r≠7 → r≠2*i+1 → r≠cap+1+i → t.index r=s.index r

private theorem move_spec (P : K→Prop) (s : Memory K) (cap i val : ℕ) (hs : s.AllData P)
    (lo : 6 ≤ i) (hi : 2*i+1 ≤ cap) (h3 : s.index 3=cap+1+i) (h4 : s.index 4=2*i+1)
    (h5 : s.index 5=0) (hx : s.index (cap+1+i)=val) :
    ∃ t, Eval (Memory.AllData P) (program moveOps) s 6 t ∧ DidMove s t cap i val := by
  let t := applyOps moveOps s
  refine ⟨t,ops_spec P moveOps s hs,ops_data ..,?_,?_,?_,?_,?_⟩
  all_goals try (intro r h3' h4' h7' ho hh)
  all_goals simp (disch := omega) [t,moveOps,applyOps,AddressOp.apply,h3,h4,h5,hx]
  all_goals omega

private structure Moving (P : K→Prop) (s : Memory K) (cap : ℕ) (f : ℕ→ℕ)
    (i : ℕ) (t : Memory K) : Prop where
  safe : t.AllData P
  data : t.data=s.data
  capReg : t.index 0=cap
  highPtr : t.index 3=cap+1+i
  oddPtr : t.index 4=2*i+1
  zero : t.index 5=0
  upper : t.index 6=cap+1
  done : ∀ j, 6 ≤ j → j < i → t.index (2*j+1)=f j ∧ t.index (cap+1+j)=0
  frame : ∀ r, 11 < r → (∀ j, 6 ≤ j → j < i → r≠2*j+1 ∧ r≠cap+1+j) → t.index r=s.index r

theorem scatterBlock_spec (P : K→Prop) (s : Memory K) (cap : ℕ) (f : ℕ→ℕ)
    (hs : s.AllData P) (hc : 64 ≤ cap) (h0 : s.index 0=cap)
    (hw : ∀ i < (cap+1)/2, s.index (cap+1+i)=f i) :
    ∃ t, Eval (Memory.AllData P) scatterBlock s (10+(((cap+1)/2-6)*8+1)) t ∧
      t.data=s.data ∧ t.index 0=cap ∧
      (∀ j, 6 ≤ j → j < (cap+1)/2 → t.index (2*j+1)=f j ∧ t.index (cap+1+j)=0) ∧
      ∀ r, 11 < r → (∀ j, 6 ≤ j → j < (cap+1)/2 → r≠2*j+1 ∧ r≠cap+1+j) → t.index r=s.index r := by
  let a := applyOps initOps s
  let I := fun j => Moving P s cap f (6+j)
  have ea := ops_spec P initOps s hs
  have init : I 0 a := by
    refine ⟨ea.safe_end,ops_data ..,?_,?_,?_,?_,?_,fun j h1 h2 => (by omega),?_⟩
    all_goals try (intro r hr _)
    all_goals simp (disch := omega) [a,initOps,applyOps,AddressOp.apply,h0]
  obtain ⟨t,run,out⟩ := Eval.loop_invariant_exact (safe:=Memory.AllData P) (c:=.addrLT 4 6)
    (body:=program moveOps) I a ((cap+1)/2-6) 6 init
    (by
      intro j hj u h
      let i := 6+j
      have il : 6 ≤ i := by dsimp [i]; omega
      have ih : 2*i+1 ≤ cap := by dsimp [i]; omega
      have guard : (Cond.addrLT 4 6).test u=true := by
        simp only [Cond.test,decide_eq_true_eq,h.oddPtr,h.upper]
        omega
      have src : u.index (cap+1+i)=f i :=
        (h.frame _ (by omega) (by intro l hl hlt; change l < i at hlt; constructor <;> omega)).trans
          (hw i (by omega))
      obtain ⟨z,step,zz⟩ := move_spec P u cap i (f i) h.safe il ih h.highPtr h.oddPtr h.zero src
      refine ⟨guard,z,step,step.safe_end,zz.data.trans h.data,?_,zz.p3,zz.p4,?_,?_,?_,?_⟩
      · exact (zz.frame 0 (by decide) (by decide) (by decide) (by omega) (by omega)).trans h.capReg
      · exact (zz.frame 5 (by decide) (by decide) (by decide) (by omega) (by omega)).trans h.zero
      · exact (zz.frame 6 (by decide) (by decide) (by decide) (by omega) (by omega)).trans h.upper
      · intro l hl hlt
        change l < i+1 at hlt
        by_cases eq : l=i
        · simpa [eq] using And.intro zz.odd zz.high
        · have prev := h.done l hl (by change l < i; omega)
          exact ⟨(zz.frame _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans prev.1,
            (zz.frame _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans prev.2⟩
      · intro r hr miss
        have cuts := miss i il (by change i < i+1; omega)
        exact (zz.frame _ (by omega) (by omega) (by omega) cuts.1 cuts.2).trans
          (h.frame r hr (fun l hl hlt => miss l hl (by omega))))
    (by
      intro u h
      refine ⟨?_,h.safe⟩
      simp only [Cond.test,decide_eq_false_iff_not,h.oddPtr,h.upper]
      omega)
  have total : 6+((cap+1)/2-6)=(cap+1)/2 := by omega
  refine ⟨t,ea.seq run,out.data,out.capReg,?_,?_⟩
  · simpa only [total] using out.done
  · simpa only [total] using out.frame

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
