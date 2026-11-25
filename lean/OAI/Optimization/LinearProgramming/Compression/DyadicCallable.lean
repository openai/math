import OAI.Optimization.LinearProgramming.Compression.DyadicQueryCallRAM
import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.CallableOddBlock

/-! Native reentrant bisection. All persistent caller registers, including
indirect array pointers, occupy the odd bank. The even bank can be repopulated
for every native sign call. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace DyadicRAM
open RAM RAM.Callable OAI.Optimization.LinearProgramming.Lattice

/-- The same logical block can run on any pair of physical register banks,
with native scratch isolated from the caller. -/
def oddLeaf (b : Block) : Fragment := Fragment.ofBlock (Odd.block b)

theorem oddLeaf_run {P : ℚ → Prop} (c : Memory ℚ) (hc : c.AllData P) {m t : Memory ℚ}
    {b : Block} {k : ℕ} (he : Block.Eval (Memory.AllData P) b m k t) :
    (oddLeaf b).Run P (Odd.memory c m) (4*k) (Odd.memory c t) := by
  obtain ⟨l,hl,e⟩ := Odd.block_eval P c hc he
  exact (Fragment.Run.ofBlock e).mono hl

theorem callee_safe {P : ℚ → Prop} {c m : Memory ℚ} (h : (Odd.memory c m).AllData P) :
    c.AllData P := fun i => by simpa only [Odd.data_even] using h (2*i)

theorem caller_safe {P : ℚ → Prop} {c m : Memory ℚ} (h : (Odd.memory c m).AllData P) :
    m.AllData P := fun i => by simpa only [Odd.data_slot] using h (Odd.slot i)

/-- A native call is allowed to replace the even bank. Each invocation must
restore the caller registers in its ABI and leave the even bank ready to serve
the next query. The ready predicate may for example impose a scratch window. -/
def FragmentAnswers {p : ℕ} (call : Fragment) (oracle : (Fin p → ℤ) → Bool)
    (a b : Fin p → ℤ) (k B : ℕ) (P : ℚ → Prop) (ready frame : Memory ℚ → Prop) : Prop :=
  ∀ j < k, ∀ c m, c.AllData P → ready c → At oracle a b k P frame j m →
    ∃ d t, call.Run P (Odd.memory c m) B (Odd.memory d t) ∧ ready d ∧
      At oracle a b k P frame j t ∧ t.data 2=(replyDigit oracle a b j:ℚ)

/-- The native sign service is a relocatable fragment. The fixed caller
initializes the numerator and denominator, loops for the precision in
address register zero, and updates each by the returned signed digit. -/
def searchFragment (call : Fragment) : Fragment :=
  .seq (oddLeaf (.straight [.const 0 0, .const 1 1, .addrConst 1 0]))
    (.loop (Odd.cond (.addrLT 1 0))
      (.seq call (oddLeaf (.seq advance (.op (.incr 1 1))))))

/-- Exact bisection arithmetic, branch semantics, every intermediate register,
and an instruction bound including the physical odd/even encoding and calls. -/
theorem searchFragment_run {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k B : ℕ) (P : ℚ → Prop) (hP : ∀ n : ℤ, |n| ≤ 2^k → P n)
    (ready frame : Memory ℚ → Prop) (hf : Stable frame) (call : Fragment)
    (hcall : FragmentAnswers call oracle a b k B P ready frame)
    (c m : Memory ℚ) (hc : c.AllData P) (hr : ready c) (hm : m.AllData P)
    (hframe : frame m) (hprec : m.index 0=k) :
    ∃ d t, (searchFragment call).Run P (Odd.memory c m) (k*(B+18)+13) (Odd.memory d t) ∧
      ready d ∧ At oracle a b k P frame k t := by
  let m₀ := m.putData 0 0
  let m₁ := m₀.putData 1 1
  let m₂ := m₁.putIndex 1 0
  have hp₀ : P 0 := by simpa using hP 0 (by positivity)
  have hp₁ : P 1 := by simpa using hP 1 (by simp [one_le_pow₀ (by decide : (1:ℤ) ≤ 2)])
  have s₀ : m₀.AllData P := hm.putData 0 hp₀
  have s₁ : m₁.AllData P := s₀.putData 1 hp₁
  have s₂ : m₂.AllData P := s₁
  have f₀ : frame m₀ := hf.scalar m hframe 0 (by decide) 0
  have f₁ : frame m₁ := hf.scalar m₀ f₀ 1 (by decide) 1
  have start : At oracle a b k P frame 0 m₂ := by
    refine ⟨s₂,hf.counter _ f₁ _,by simpa [m₂,m₁,m₀] using hprec,by simp [m₂],
      by simp [m₂,m₁,m₀,dyadicSearch],by simp [m₂,m₁]⟩
  have ei : Block.Eval (Memory.AllData P) (.straight [.const 0 0, .const 1 1, .addrConst 1 0]) m 3 m₂ :=
    (Block.Eval.op_const m 0 0 hm s₀).seq ((Block.Eval.op_const m₀ 1 1 s₀ s₁).seq
      ((Block.Eval.op_addrConst m₁ 1 0 s₁ s₂).seq (.skip s₂)))
  let I (j : ℕ) (st : Memory ℚ) := ∃ v z, st=Odd.memory v z ∧ v.AllData P ∧ ready v ∧ At oracle a b k P frame j z
  have init : I 0 (Odd.memory c m₂) := ⟨c,m₂,rfl,hc,hr,start⟩
  let body := Fragment.seq call (oddLeaf (.seq advance (.op (.incr 1 1))))
  have run := Fragment.Run.loop_invariant (P:=P) (Odd.cond (.addrLT 1 0)) body I k (B+16)
    (Odd.memory c m₂) init (by
      rintro j hj _ ⟨v,z,rfl,hv,hready,hz⟩
      obtain ⟨v',z',ec,hr',hz',digit⟩ := hcall j hj v z hv hready hz
      have hv' := callee_safe ec.safe_end
      obtain ⟨y,ea,hy⟩ := advance_eval oracle a b hj hP hf hz' digit
      let y' := y.putIndex 1 (y.index 1+1)
      have en : Block.Eval (Memory.AllData P) (.op (.incr 1 1)) y 1 y' :=
        Block.Eval.op_incr y 1 1 ea.safe_end hy.safe
      refine ⟨by rw [Odd.cond_test];simp [Cond.test,hz.cursor,hz.limit,hj],
        Odd.memory v' y',ec.seq (oddLeaf_run v' hv' (ea.seq en)),v',y',rfl,hv',hr',hy⟩)
    (by
      rintro _ ⟨v,z,rfl,hv,_,hz⟩
      refine ⟨by rw [Odd.cond_test];simp [Cond.test,hz.cursor,hz.limit],
        Odd.allData v z hv hz.safe⟩)
  obtain ⟨_,et,d,t,rfl,_,hready,ht⟩ := run
  refine ⟨d,t,(Fragment.Run.seq (oddLeaf_run c hc ei) et).mono ?_,hready,ht⟩
  simp only [show B+16+2=B+18 by omega]
  omega

end DyadicRAM
end Compression
end LinearProgramming
end Optimization
end OAI
