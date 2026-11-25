import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Convert one scalar word directly into the even native address representation.
Both geometric zero scratch registers are restored; the surrounding caller is unchanged. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM RAM.Block RAM.Callable

def decodeScalarWord (pointer dst : ℕ) : Block :=
  .seq (.straight [.load (Odd.slot 2) pointer,.addrConst dst 0]) <|
  .seq (.loop (.scalarLT (Odd.slot 29) (Odd.slot 2)) (.straight [
    .add (Odd.slot 29) (Odd.slot 29) (Odd.slot 3),.incr dst dst,.incr dst dst]))
    (.straight [.const (Odd.slot 2) 0,.const (Odd.slot 29) 0])

private structure ScalarCount (m : Memory ℚ) (P : ℚ → Prop) (dst value j : ℕ) (s : Memory ℚ) : Prop where
  safe : s.AllData P
  token : s.data (Odd.slot 2)=(value:ℚ)
  current : s.data (Odd.slot 29)=(j:ℚ)
  one : s.data (Odd.slot 3)=1
  numeric : s.index dst=2*j
  scalarFrame (a) : a ≠ Odd.slot 2 → a ≠ Odd.slot 29 → s.data a=m.data a
  addressFrame (a) : a ≠ dst → s.index a=m.index a

private theorem words_memory_eq {a b : Memory ℚ} (hd : ∀i,a.data i=b.data i) (hi : ∀i,a.index i=b.index i) : a=b := by
  cases a; cases b
  congr <;> funext i
  · exact hd i
  · exact hi i

/-- This allows the pointer and native destination to be the same register, which
is used when the first four requested native words are written individually. -/
theorem decodeScalarWord_eval (m : Memory ℚ) (P : ℚ → Prop) (pointer dst v : ℕ) (hm : m.AllData P)
    (token : m.data (m.index pointer)=(v:ℚ)) (zero2 : m.data (Odd.slot 2)=0)
    (zero29 : m.data (Odd.slot 29)=0) (one3 : m.data (Odd.slot 3)=1)
    (hnum : ∀ i ≤ v,P (i:ℚ)) :
    Eval (Memory.AllData P) (decodeScalarWord pointer dst) m (5*v+5) (m.putIndex dst (2*v)) := by
  let a := m.putData (Odd.slot 2) (v:ℚ)
  let b := a.putIndex dst 0
  have ea : Eval (Memory.AllData P) (.op (.load (Odd.slot 2) pointer)) m 1 a := by
    simpa [a,token] using Eval.op_load m (Odd.slot 2) pointer hm (hm.putData _ (hm _))
  have eb : Eval (Memory.AllData P) (.op (.addrConst dst 0)) a 1 b := Eval.op_addrConst a dst 0 ea.safe_end ea.safe_end
  have init : ScalarCount m P dst v 0 b := by
    refine ⟨eb.safe_end,by simp [b,a],?_,?_,by simp [b],?_,?_⟩
    · simpa [b,a,Odd.slot] using zero29
    · simpa [b,a,Odd.slot] using one3
    · intro p ne _; simp [b,a,ne]
    · intro p ne; simp [b,a,ne]
  obtain ⟨t,run,inv⟩ := Eval.loop_invariant_exact (c := .scalarLT (Odd.slot 29) (Odd.slot 2))
    (body := .straight [.add (Odd.slot 29) (Odd.slot 29) (Odd.slot 3),.incr dst dst,.incr dst dst])
    (ScalarCount m P dst v) b v 3 init (by
      intro j hj u h
      have guard : (Cond.scalarLT (Odd.slot 29) (Odd.slot 2)).test u=true := by
        simp [Cond.test,h.current,h.token,hj]
      have sum : u.data (Odd.slot 29)+u.data (Odd.slot 3)=((j+1:ℕ):ℚ) := by simp [h.current,h.one]
      let c := u.putData (Odd.slot 29) ((j+1:ℕ):ℚ)
      let d := c.putIndex dst (2*j+1)
      let e := d.putIndex dst (2*j+2)
      have ec : Eval (Memory.AllData P) (.op (.add (Odd.slot 29) (Odd.slot 29) (Odd.slot 3))) u 1 c := by
        simpa [c,sum] using Eval.op_add u (Odd.slot 29) (Odd.slot 29) (Odd.slot 3) h.safe (h.safe.putData _ (sum ▸ hnum _ hj))
      have ed : Eval (Memory.AllData P) (.op (.incr dst dst)) c 1 d := by
        simpa [d,c,h.numeric] using Eval.op_incr c dst dst ec.safe_end ec.safe_end
      have ee : Eval (Memory.AllData P) (.op (.incr dst dst)) d 1 e := by
        simpa [e,d] using Eval.op_incr d dst dst ed.safe_end ed.safe_end
      refine ⟨guard,e,ec.seq (ed.seq (ee.seq (.skip ee.safe_end))),ee.safe_end,?_,?_,?_,?_,?_,?_⟩
      · simpa [e,d,c,Odd.slot] using h.token
      · simp [e,d,c]
      · simpa [e,d,c,Odd.slot] using h.one
      · simp [e,Nat.mul_add]
      · intro p hn h29; simp [e,d,c,h29,h.scalarFrame p hn h29]
      · intro p hp; simp [e,d,c,hp,h.addressFrame p hp]) (by
      intro t h
      exact ⟨by simp [Cond.test,h.current,h.token],h.safe⟩)
  let x := t.putData (Odd.slot 2) 0
  let z := x.putData (Odd.slot 29) 0
  have zero : P 0 := zero2 ▸ hm (Odd.slot 2)
  have ex : Eval (Memory.AllData P) (.op (.const (Odd.slot 2) 0)) t 1 x := by
    simpa [x] using Eval.op_const t (Odd.slot 2) 0 run.safe_end (run.safe_end.putData _ (by simpa only [Rat.cast_zero] using zero))
  have ez : Eval (Memory.AllData P) (.op (.const (Odd.slot 29) 0)) x 1 z := by
    simpa [z] using Eval.op_const x (Odd.slot 29) 0 ex.safe_end (ex.safe_end.putData _ (by simpa only [Rat.cast_zero] using zero))
  have target : z=m.putIndex dst (2*v) := by
    apply words_memory_eq
    · intro i
      by_cases h2 : i=Odd.slot 2
      · subst i; simp [z,x,Odd.slot] at zero2 ⊢; exact zero2.symm
      by_cases h29 : i=Odd.slot 29
      · subst i; simpa [z] using zero29.symm
      · simp [z,x,h2,h29,inv.scalarFrame i h2 h29]
    · intro i
      by_cases hit : i=dst
      · subst i; simpa [z,x] using inv.numeric
      · simp [z,x,hit,inv.addressFrame i hit]
  rw [← target]
  have start := ea.seq (eb.seq (.skip eb.safe_end))
  have finish := ex.seq (ez.seq (.skip ez.safe_end))
  exact (show (1+(1+0))+(v*(3+2)+1+(1+(1+0)))=5*v+5 by omega) ▸ start.seq (run.seq finish)

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
