import OAI.Optimization.LinearProgramming.Recovery.SupportRAM

/-! Exact caller frame of the actual support-vector edits, independent of the callback
and of the numbers held in the protected matrix/tape region. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportRAM

open RAM

universe u
variable {K : Type u}

structure Frame (base n : ℕ) (a b : Memory K) : Prop where
  data : ∀ p, p≠150 → p≠151 → (p<base ∨ base+n ≤ p) → b.data p=a.data p
  index : ∀ p, p≠152 → p≠153 → p≠154 → p≠155 → b.index p=a.index p

def StableContext (base n : ℕ) (context : Memory K → Prop) : Prop :=
  ∀ {a b}, context a → Frame base n a b → context b

theorem Frame.refl (base n : ℕ) (m : Memory K) : Frame base n m m :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem Frame.trans {base n : ℕ} {a b c : Memory K} (f : Frame base n a b) (g : Frame base n b c) :
    Frame base n a c :=
  ⟨fun p h j k => (g.data p h j k).trans (f.data p h j k),
   fun p h i j k => (g.index p h i j k).trans (f.index p h i j k)⟩

theorem Frame.put_scalar (base n : ℕ) (m : Memory K) (j : ℕ) (x : K)
    (allowed : j=150 ∨ j=151 ∨ base≤j ∧ j<base+n) : Frame base n m (m.putData j x) := by
  refine ⟨?_,fun _ _ _ _ _ => rfl⟩
  intro p h150 h151 outside
  exact Memory.putData_ne _ (by omega : p≠j) _

theorem Frame.put_index (base n : ℕ) (m : Memory K) (j x : ℕ)
    (allowed : j=152 ∨ j=153 ∨ j=154 ∨ j=155) : Frame base n m (m.putIndex j x) := by
  refine ⟨fun _ _ _ _ => rfl,?_⟩
  intro p h152 h153 h154 h155
  exact Memory.putIndex_ne _ (by omega : p≠j) _

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem execution_end {p : Program} {P Q : State K → Prop} {m t z : State K} {k : ℕ}
    (x : Execution p P m k t) (y : Execution p Q m k z) : t=z := by
  induction x generalizing z with
  | done s _ => cases y; rfl
  | next _ first _ ih =>
    cases y with
    | next _ second tail =>
      have eq := Option.some.inj (first.symm.trans second)
      cases eq
      exact ih tail

private theorem eval_end {P Q : Memory K → Prop} {b : Block} {m t z : Memory K} {k : ℕ}
    (x : Block.Eval P b m k t) (y : Block.Eval Q b m k z) : t=z :=
  congrArg State.memory (execution_end (x.compile_correct (CodeAt.whole (b.compile 0)))
    (y.compile_correct (CodeAt.whole (b.compile 0))))

theorem clear_frame {base n : ℕ} {S : Finset (Fin n)} (j : Fin n) (m t : Memory K)
    (h : Layout m base j.val S) {P : Memory K → Prop} (run : Block.Eval P clear m 3 t) :
    Frame base n m t := by
  let a := m.putData 150 (m.data (m.index 153))
  let b := a.putData 151 (0:K)
  let u := b.putData (b.index 153) (b.data 151)
  have load : Block.Eval (fun _ : Memory K => True) (.op (.load 150 153)) m 1 a :=
    Block.Eval.op_load _ _ _ trivial trivial
  have zero : Block.Eval (fun _ : Memory K => True) (.op (.const 151 0)) a 1 b := by
    simpa only [Rat.cast_zero] using
      Block.Eval.op_const (safe := fun _ : Memory K => True) a 151 0 trivial trivial
  have store : Block.Eval (fun _ : Memory K => True) (.op (.store 153 151)) b 1 u :=
    Block.Eval.op_store _ _ _ trivial trivial
  rw [eval_end run (load.seq (zero.seq store))]
  have src : base ≤ b.index 153 ∧ b.index 153 < base+n := by
    change base ≤ m.index 153 ∧ m.index 153 < base+n
    rw [h.2.2.2.1]
    have := j.isLt
    omega
  exact ((Frame.put_scalar base n m 150 _ (Or.inl rfl)).trans
    (Frame.put_scalar base n a 151 _ (Or.inr (Or.inl rfl)))).trans
    (Frame.put_scalar base n b _ _ (Or.inr (Or.inr src)))

theorem reply_frame {base n : ℕ} {S : Finset (Fin n)} (j : Fin n) (m t : Memory K)
    (h : Layout m base j.val S) (answer : Bool) (ha : m.index 154=answer.toNat)
    {P : Memory K → Prop} (run : Block.Eval P applyReply m 3 t) : Frame base n m t := by
  let a := m.putIndex 155 0
  have op : Block.Eval (fun _ : Memory K => True) (.op (.addrConst 155 0)) m 1 a :=
    Block.Eval.op_addrConst _ _ _ trivial trivial
  have fa : Frame base n m a := Frame.put_index base n m 155 0 (by decide)
  cases answer with
  | true =>
    have test : (Cond.addrLT 155 154).test a=true := by simp [Cond.test,a,ha]
    have branch : Block.Eval (fun _ : Memory K => True)
        (.branch (.addrLT 155 154) .skip (.op (.store 153 150))) a 2 a :=
      .branchTrue test (.skip trivial)
    rw [eval_end run (op.seq branch)]
    exact fa
  | false =>
    have test : (Cond.addrLT 155 154).test a=false := by simp [Cond.test,a,ha]
    let u := a.putData (a.index 153) (a.data 150)
    have write : Block.Eval (fun _ : Memory K => True) (.op (.store 153 150)) a 1 u :=
      Block.Eval.op_store _ _ _ trivial trivial
    have branch : Block.Eval (fun _ : Memory K => True)
        (.branch (.addrLT 155 154) .skip (.op (.store 153 150))) a 2 u := .branchFalse test write
    rw [eval_end run (op.seq branch)]
    have src : base ≤ a.index 153 ∧ a.index 153 < base+n := by
      change base ≤ m.index 153 ∧ m.index 153 < base+n
      rw [h.2.2.2.1]
      have := j.isLt
      omega
    exact fa.trans (Frame.put_scalar base n a _ _ (Or.inr (Or.inr src)))

theorem advance_frame (base n : ℕ) (m t : Memory K) {P : Memory K → Prop}
    (run : Block.Eval P advance m 2 t) : Frame base n m t := by
  let a := m.putIndex 152 (m.index 152+1)
  let u := a.putIndex 153 (a.index 153+1)
  have first : Block.Eval (fun _ : Memory K => True) (.op (.incr 152 152)) m 1 a :=
    Block.Eval.op_incr _ _ _ trivial trivial
  have second : Block.Eval (fun _ : Memory K => True) (.op (.incr 153 153)) a 1 u :=
    Block.Eval.op_incr _ _ _ trivial trivial
  rw [eval_end run (first.seq second)]
  exact (Frame.put_index base n m 152 _ (by decide)).trans (Frame.put_index base n a 153 _ (by decide))


end SupportRAM
end Recovery
end LinearProgramming
end Optimization
end OAI
