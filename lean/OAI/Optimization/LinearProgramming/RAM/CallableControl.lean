import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Structured control flow around relocatable fragments, including native subroutine calls. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Fragment

def seq (a b : Fragment) : Fragment where
  size := a.size+b.size
  emit pc := a.emit pc ++ b.emit (pc+a.size)
  length_emit pc := by simp [a.length_emit, b.length_emit]

def branch (c : Cond) (a b : Fragment) : Fragment where
  size := 1+a.size+1+b.size
  emit pc :=
    let no := pc+1+a.size+1
    c.instr (pc+1) no :: (a.emit (pc+1) ++ (.jump (no+b.size) :: b.emit no))
  length_emit pc := by simp [a.length_emit, b.length_emit]; omega

def loop (c : Cond) (a : Fragment) : Fragment where
  size := 1+a.size+1
  emit pc := c.instr (pc+1) (pc+1+a.size+1) :: (a.emit (pc+1) ++ [.jump pc])
  length_emit pc := by simp [a.length_emit]; omega

private theorem branch_parts {p pc c a b} (h : CodeAt p pc ((branch c a b).emit pc)) :
    let no := pc+1+a.size+1
    p[pc]?=some (c.instr (pc+1) no) ∧ CodeAt p (pc+1) (a.emit (pc+1)) ∧
      p[pc+1+a.size]?=some (.jump (no+b.size)) ∧ CodeAt p no (b.emit no) := by
  let no := pc+1+a.size+1
  have whole : CodeAt p pc (c.instr (pc+1) no :: (a.emit (pc+1) ++ (.jump (no+b.size) :: b.emit no))) := h
  have tail := Block.Eval.tail_at whole
  have hr := tail.right
  rw [a.length_emit] at hr
  exact ⟨whole.head, tail.left, hr.head, Block.Eval.tail_at hr⟩

private theorem loop_parts {p pc c a} (h : CodeAt p pc ((loop c a).emit pc)) :
    p[pc]?=some (c.instr (pc+1) (pc+1+a.size+1)) ∧ CodeAt p (pc+1) (a.emit (pc+1)) ∧
      p[pc+1+a.size]?=some (.jump pc) := by
  have whole : CodeAt p pc (c.instr (pc+1) (pc+1+a.size+1) :: (a.emit (pc+1) ++ [.jump pc])) := h
  have tail := Block.Eval.tail_at whole
  have hr := tail.right
  rw [a.length_emit] at hr
  exact ⟨whole.head,tail.left,hr.head⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {P : K → Prop} {s t u : Memory K} {j k : ℕ} {a b : Fragment} {c : Cond}

theorem Run.seq (ha : a.Run P s j t) (hb : b.Run P t k u) : (seq a b).Run P s (j+k) u := by
  intro p pc h
  change CodeAt p pc (a.emit pc ++ b.emit (pc+a.size)) at h
  have hr := h.right
  rw [a.length_emit] at hr
  obtain ⟨x,hx,ex⟩ := ha p pc h.left
  obtain ⟨y,hy,ey⟩ := hb p _ hr
  exact ⟨x+y, Nat.add_le_add hx hy, by simpa [Fragment.seq,Nat.add_assoc] using ex.append ey⟩

theorem Run.branchTrue (hc : c.test s=true) (ha : a.Run P s j t) (b : Fragment) :
    (branch c a b).Run P s (1+j+1) t := by
  intro p pc h
  obtain ⟨head,yes,jump,_⟩ := branch_parts h
  obtain ⟨x,hx,body⟩ := ha p _ yes
  have first := Block.Eval.test_exec (safe := fun z : Memory K => ∀ i, P (z.data i)) p c s pc _ _ ha.safe_start head
  simp [hc] at first
  have last := Block.Eval.jump_exec (safe := fun z : Memory K => ∀ i, P (z.data i)) p _ _ t ha.safe_end jump
  exact ⟨1+x+1,by omega, by simpa [branch,State.memory,Nat.add_assoc] using (first.append body).append last⟩

theorem Run.branchFalse (hc : c.test s=false) (a : Fragment) (hb : b.Run P s k t) :
    (branch c a b).Run P s (1+k) t := by
  intro p pc h
  obtain ⟨head,_,_,no⟩ := branch_parts h
  obtain ⟨x,hx,body⟩ := hb p _ no
  have first := Block.Eval.test_exec (safe := fun z : Memory K => ∀ i, P (z.data i)) p c s pc _ _ hb.safe_start head
  simp [hc] at first
  exact ⟨1+x,by omega,by simpa [branch,State.memory,Nat.add_assoc] using first.append body⟩

theorem Run.loopFalse (hc : c.test s=false) (hs : ∀ i, P (s.data i)) (a : Fragment) :
    (loop c a).Run P s 1 s := by
  intro p pc h
  obtain ⟨head,_,_⟩ := loop_parts h
  have first := Block.Eval.test_exec (safe := fun z : Memory K => ∀ i, P (z.data i)) p c s pc _ _ hs head
  exact ⟨1,le_rfl,by simpa [hc,loop,State.memory,Nat.add_assoc] using first⟩

theorem Run.loopTrue (hc : c.test s=true) (ha : a.Run P s j t) (hrest : (loop c a).Run P t k u) :
    (loop c a).Run P s (1+j+1+k) u := by
  intro p pc h
  obtain ⟨head,yes,jump⟩ := loop_parts h
  obtain ⟨x,hx,body⟩ := ha p _ yes
  obtain ⟨y,hy,rest⟩ := hrest p pc h
  have first := Block.Eval.test_exec (safe := fun z : Memory K => ∀ i, P (z.data i)) p c s pc _ _ ha.safe_start head
  simp [hc] at first
  have back := Block.Eval.jump_exec (safe := fun z : Memory K => ∀ i, P (z.data i)) p _ _ t ha.safe_end jump
  exact ⟨1+x+1+y,by omega,by simpa [State.memory] using ((first.append body).append back).append rest⟩

/-- Every guard, back jump, and subroutine instruction is counted along the same physical trace. -/
theorem Run.loop_invariant (c : Cond) (a : Fragment) (I : ℕ → Memory K → Prop) (n budget : ℕ)
    (s : Memory K) (hs : I 0 s)
    (step : ∀ i<n, ∀ m, I i m → c.test m=true ∧ ∃ t, a.Run P m budget t ∧ I (i+1) t)
    (stop : ∀ m, I n m → c.test m=false ∧ ∀ x,P (m.data x)) :
    ∃ t, (loop c a).Run P s (n*(budget+2)+1) t ∧ I n t := by
  have go (rem : ℕ) : ∀ i, i+rem=n → ∀ m, I i m →
      ∃ t, (loop c a).Run P m (rem*(budget+2)+1) t ∧ I n t := by
    induction rem with
    | zero =>
      intro i h m hi
      have ix : i=n := by omega
      subst i
      obtain ⟨hstop,ok⟩ := stop m hi
      exact ⟨m,by simpa using Run.loopFalse hstop ok a,hi⟩
    | succ rem ih =>
      intro i h m hi
      obtain ⟨guard,v,one,hv⟩ := step i (by omega) m hi
      obtain ⟨t,tail,ht⟩ := ih (i+1) (by omega) v hv
      exact ⟨t,(Run.loopTrue guard one tail).mono (by rw [Nat.succ_mul]; omega),ht⟩
  exact go n 0 (by simp) s hs

/-- Initialize and increment a runtime address counter around an arbitrary fragment body. -/
def forRange (idx size : ℕ) (body : Fragment) : Fragment := seq
  (ofBlock (.op (.addrConst idx 0)))
  (loop (.addrLT idx size) (seq body (ofBlock (.op (.incr idx idx)))))

theorem Run.forRange_invariant (idx size n budget : ℕ) (body : Fragment) (I : ℕ → Memory K → Prop)
    (s : Memory K) (hs : ∀ i,P (s.data i)) (hi : I 0 (s.putIndex idx 0))
    (hI : ∀ i s, I i s → (∀ j,P (s.data j)) ∧ s.index idx=i ∧ s.index size=n)
    (hb : ∀ i<n, ∀ m, I i m → ∃ t, body.Run P m budget t ∧ I (i+1) (t.putIndex idx (t.index idx+1))) :
    ∃ t, (forRange idx size body).Run P s (n*(budget+3)+2) t ∧ I n t := by
  have init := Run.ofBlock (Block.Eval.op_addrConst (safe := fun z : Memory K => ∀ i,P (z.data i)) s idx 0 hs hs)
  obtain ⟨t,hr,ht⟩ := Run.loop_invariant (.addrLT idx size) (Fragment.seq body (Fragment.ofBlock (.op (.incr idx idx)))) I n (budget+1)
    (s.putIndex idx 0) hi (by
      intro i hn m hm
      obtain ⟨_,hidx,hsize⟩ := hI i m hm
      obtain ⟨u,exec,hnext⟩ := hb i hn m hm
      have inc := Run.ofBlock (Block.Eval.op_incr (safe := fun z : Memory K => ∀ j,P (z.data j))
        u idx idx exec.safe_end ((hI _ _ hnext).1))
      exact ⟨by simp [Cond.test,hidx,hsize,hn],_,exec.seq inc,hnext⟩) (by
      intro m hm
      obtain ⟨valid,hidx,hsize⟩ := hI n m hm
      exact ⟨by simp [Cond.test,hidx,hsize],valid⟩)
  exact ⟨t,(init.seq hr).mono (by rw [show budget+1+2=budget+3 by omega]; omega),ht⟩

end Fragment
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
