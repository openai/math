import OAI.Optimization.LinearProgramming.RAM.Code

/-! Counted loops and straight-line programs in the step-counting RAM semantics. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

variable {K : Type*}

/-- Assemble a list of consecutive primitive instructions into one block. -/
def Block.straight : List Instr → Block
  | [] => .skip
  | i :: rest => .seq (.op i) (Block.straight rest)

@[simp] theorem Block.size_straight (is : List Instr) : (Block.straight is).size = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [Block.straight, Block.size, ih, Nat.add_comm]

/-- The loop counter is initialized once and advanced after every callback. -/
def Block.forRange (idx size : Nat) (body : Block) : Block :=
  .seq (.op (.addrConst idx 0)) (.loop (.addrLT idx size) (.seq body (.op (.incr idx idx))))

/-- Row-major traversal of a rectangular array with independent row and column registers. -/
def Block.forRowsCols (row rows col cols : Nat) (body : Block) : Block :=
  .forRange row rows (.forRange col cols body)

@[simp] theorem Memory.putData_index (m : Memory K) (dst : Nat) (x : K) :
    (m.putData dst x).index = m.index := rfl

@[simp] theorem Memory.putIndex_data (m : Memory K) (dst val : Nat) :
    (m.putIndex dst val).data = m.data := rfl

@[simp] theorem Memory.putData_same (m : Memory K) (dst : Nat) (x : K) :
    (m.putData dst x).data dst = x := Function.update_self ..

@[simp] theorem Memory.putData_ne (m : Memory K) {k dst : Nat} (h : k ≠ dst) (x : K) :
    (m.putData dst x).data k = m.data k := Function.update_of_ne h ..

@[simp] theorem Memory.putIndex_same (m : Memory K) (dst val : Nat) :
    (m.putIndex dst val).index dst = val := Function.update_self ..

@[simp] theorem Memory.putIndex_ne (m : Memory K) {k dst : Nat} (h : k ≠ dst) (val : Nat) :
    (m.putIndex dst val).index k = m.index k := Function.update_of_ne h ..

namespace Block.Eval

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {safe : Memory K → Prop} {c : Cond} {body : Block}

/-- A loop with exactly `n` iterations, all of equal cost, given its boundary states.
The remaining unit is the final false guard. -/
theorem loop_fixed (state : Nat → Memory K) (n cost : Nat)
    (hbody : ∀ j < n, c.test (state j) = true ∧
      Eval safe body (state j) cost (state (j+1)))
    (hstop : c.test (state n) = false) (hs : safe (state n)) :
    Eval safe (.loop c body) (state 0) (n*(cost+2)+1) (state n) := by
  induction n generalizing state with
  | zero => simpa using Eval.loopFalse hstop hs
  | succ n ih =>
    obtain ⟨test, first⟩ := hbody 0 (Nat.zero_lt_succ _)
    have rest := ih (fun j => state (j+1))
      (fun j hj => hbody (j+1) (Nat.succ_lt_succ hj)) hstop hs
    rw [Nat.succ_mul]
    convert Eval.loopTrue test first rest using 1
    omega

/-- Bound the whole loop from a boundary invariant and a bound on one iteration.
The state and time of each iteration may depend on the data. -/
theorem loop_invariant (I : Nat → Memory K → Prop) (m : Memory K) (n B : Nat)
    (hstart : I 0 m)
    (hbody : ∀ j < n, ∀ s, I j s → c.test s = true ∧
      ∃ t k, k ≤ B ∧ Eval safe body s k t ∧ I (j+1) t)
    (hstop : ∀ t, I n t → c.test t = false ∧ safe t) :
    ∃ t k, k ≤ n*(B+2)+1 ∧ Eval safe (.loop c body) m k t ∧ I n t := by
  induction n generalizing I m with
  | zero =>
    obtain ⟨test, hs⟩ := hstop m hstart
    exact ⟨m, 1, by simp, Eval.loopFalse test hs, hstart⟩
  | succ n ih =>
    obtain ⟨test, t, k, hk, first, ht⟩ := hbody 0 (Nat.zero_lt_succ _) m hstart
    obtain ⟨z, l, hl, rest, hz⟩ := ih (fun j => I (j+1)) t ht
      (fun j hj => hbody (j+1) (Nat.succ_lt_succ hj)) hstop
    exact ⟨z, 1+k+1+l, by rw [Nat.succ_mul]; omega, Eval.loopTrue test first rest, hz⟩

/-- The exact-cost variant of the invariant rule does not require preselecting boundary states. -/
theorem loop_invariant_exact (I : Nat → Memory K → Prop) (m : Memory K) (n cost : Nat)
    (hstart : I 0 m)
    (hbody : ∀ j < n, ∀ s, I j s → c.test s = true ∧
      ∃ t, Eval safe body s cost t ∧ I (j+1) t)
    (hstop : ∀ t, I n t → c.test t = false ∧ safe t) :
    ∃ t, Eval safe (.loop c body) m (n*(cost+2)+1) t ∧ I n t := by
  induction n generalizing I m with
  | zero =>
    obtain ⟨test, hs⟩ := hstop m hstart
    exact ⟨m, by simpa using Eval.loopFalse test hs, hstart⟩
  | succ n ih =>
    obtain ⟨test, t, first, ht⟩ := hbody 0 (Nat.zero_lt_succ _) m hstart
    obtain ⟨z, rest, hz⟩ := ih (fun j => I (j+1)) t ht
      (fun j hj => hbody (j+1) (Nat.succ_lt_succ hj)) hstop
    refine ⟨z, ?_, hz⟩
    rw [Nat.succ_mul]
    convert Eval.loopTrue test first rest using 1
    omega

/-- Compose a bounded, straight-line list of instructions with all intermediate states checked. -/
theorem straight (is : List Instr) (state : Nat → Memory K)
    (hstep : ∀ j : Fin is.length,
      Eval safe (.op is[j]) (state j) 1 (state (j+1)))
    (hs : safe (state is.length)) :
    Eval safe (Block.straight is) (state 0) is.length (state is.length) := by
  induction is generalizing state with
  | nil => exact .skip hs
  | cons i is ih =>
    have first := hstep ⟨0, by simp⟩
    have rest := ih (fun j => state (j+1)) (fun j => hstep j.succ) hs
    simpa [Block.straight, Nat.one_add] using Eval.seq first rest

theorem op_const (m : Memory K) (dst : Nat) (q : ℚ) (hs : safe m)
    (ht : safe (m.putData dst (q : K))) :
    Eval safe (.op (.const dst q)) m 1 (m.putData dst (q : K)) :=
  .op hs ht (fun _ => rfl)

theorem op_copy (m : Memory K) (dst src : Nat) (hs : safe m)
    (ht : safe (m.putData dst (m.data src))) :
    Eval safe (.op (.copy dst src)) m 1 (m.putData dst (m.data src)) :=
  .op hs ht (fun _ => rfl)

theorem op_add (m : Memory K) (dst x y : Nat) (hs : safe m)
    (ht : safe (m.putData dst (m.data x + m.data y))) :
    Eval safe (.op (.add dst x y)) m 1 (m.putData dst (m.data x + m.data y)) :=
  .op hs ht (fun _ => rfl)

theorem op_sub (m : Memory K) (dst x y : Nat) (hs : safe m)
    (ht : safe (m.putData dst (m.data x - m.data y))) :
    Eval safe (.op (.sub dst x y)) m 1 (m.putData dst (m.data x - m.data y)) :=
  .op hs ht (fun _ => rfl)

theorem op_mul (m : Memory K) (dst x y : Nat) (hs : safe m)
    (ht : safe (m.putData dst (m.data x * m.data y))) :
    Eval safe (.op (.mul dst x y)) m 1 (m.putData dst (m.data x * m.data y)) :=
  .op hs ht (fun _ => rfl)

theorem op_div (m : Memory K) (dst x y : Nat) (hy : m.data y ≠ 0) (hs : safe m)
    (ht : safe (m.putData dst (m.data x / m.data y))) :
    Eval safe (.op (.div dst x y)) m 1 (m.putData dst (m.data x / m.data y)) :=
  .op hs ht (fun _ => by simp [execInstr, Memory.atPC, State.putData, Memory.putData, hy])

theorem op_load (m : Memory K) (dst addr : Nat) (hs : safe m)
    (ht : safe (m.putData dst (m.data (m.index addr)))) :
    Eval safe (.op (.load dst addr)) m 1 (m.putData dst (m.data (m.index addr))) :=
  .op hs ht (fun _ => rfl)

theorem op_store (m : Memory K) (addr src : Nat) (hs : safe m)
    (ht : safe (m.putData (m.index addr) (m.data src))) :
    Eval safe (.op (.store addr src)) m 1 (m.putData (m.index addr) (m.data src)) :=
  .op hs ht (fun _ => rfl)

theorem op_addrConst (m : Memory K) (dst n : Nat) (hs : safe m)
    (ht : safe (m.putIndex dst n)) :
    Eval safe (.op (.addrConst dst n)) m 1 (m.putIndex dst n) :=
  .op hs ht (fun _ => rfl)

theorem op_addrCopy (m : Memory K) (dst src : Nat) (hs : safe m)
    (ht : safe (m.putIndex dst (m.index src))) :
    Eval safe (.op (.addrCopy dst src)) m 1 (m.putIndex dst (m.index src)) :=
  .op hs ht (fun _ => rfl)

theorem op_incr (m : Memory K) (dst src : Nat) (hs : safe m)
    (ht : safe (m.putIndex dst (m.index src + 1))) :
    Eval safe (.op (.incr dst src)) m 1 (m.putIndex dst (m.index src + 1)) :=
  .op hs ht (fun _ => rfl)

theorem op_decr (m : Memory K) (dst src : Nat) (hs : safe m)
    (ht : safe (m.putIndex dst (m.index src - 1))) :
    Eval safe (.op (.decr dst src)) m 1 (m.putIndex dst (m.index src - 1)) :=
  .op hs ht (fun _ => rfl)

theorem op_addrLoad (m : Memory K) (dst addr : Nat) (hs : safe m)
    (ht : safe (m.putIndex dst (m.index (m.index addr)))) :
    Eval safe (.op (.addrLoad dst addr)) m 1 (m.putIndex dst (m.index (m.index addr))) :=
  .op hs ht (fun _ => rfl)

theorem op_addrStore (m : Memory K) (addr src : Nat) (hs : safe m)
    (ht : safe (m.putIndex (m.index addr) (m.index src))) :
    Eval safe (.op (.addrStore addr src)) m 1 (m.putIndex (m.index addr) (m.index src)) :=
  .op hs ht (fun _ => rfl)

/-- Counted-loop invariant with explicit callback cost. The caller supplies the effects
on the invariant after the iterator has incremented its counter. -/
theorem forRange_invariant (idx size n B : Nat) (I : Nat → Memory K → Prop) (m : Memory K)
    (hs : safe m) (hi : I 0 (m.putIndex idx 0))
    (hI : ∀ j s, I j s → safe s ∧ s.index idx = j ∧ s.index size = n)
    (hb : ∀ j < n, ∀ s, I j s → ∃ t k, k ≤ B ∧ Eval safe body s k t ∧
      I (j+1) (t.putIndex idx (t.index idx+1))) :
    ∃ t k, k ≤ n*(B+3)+2 ∧ Eval safe (.forRange idx size body) m k t ∧ I n t := by
  have init := op_addrConst m idx 0 hs (hI 0 _ hi).1
  obtain ⟨t,k,hk,loop,ht⟩ := loop_invariant (safe := safe) (c := .addrLT idx size)
    (body := .seq body (.op (.incr idx idx))) I (m.putIndex idx 0) n (B+1) hi
    (by
      intro j hj s hij
      obtain ⟨_,hidx,hsize⟩ := hI j s hij
      obtain ⟨t,k,hk,run,hnext⟩ := hb j hj s hij
      refine ⟨by simp [Cond.test,hidx,hsize,hj], t.putIndex idx (t.index idx+1), k+1,
        Nat.succ_le_succ hk, run.seq ?_, hnext⟩
      exact op_incr t idx idx run.safe_end (hI _ _ hnext).1)
    (by
      intro t ht
      obtain ⟨safe',hidx,hsize⟩ := hI n t ht
      exact ⟨by simp [Cond.test,hidx,hsize], safe'⟩)
  change k ≤ n*(B+3)+1 at hk
  exact ⟨t,1+k,by omega,init.seq loop,ht⟩

/-- When the callback takes a fixed number of instructions, the entire traversal has the
exact cost `n*(cost+3)+2`, including initialization and the final guard. -/
theorem forRange_invariant_exact (idx size n cost : Nat) (I : Nat → Memory K → Prop)
    (m : Memory K) (hs : safe m) (hi : I 0 (m.putIndex idx 0))
    (hI : ∀ j s, I j s → safe s ∧ s.index idx = j ∧ s.index size = n)
    (hb : ∀ j < n, ∀ s, I j s → ∃ t, Eval safe body s cost t ∧
      I (j+1) (t.putIndex idx (t.index idx+1))) :
    ∃ t, Eval safe (.forRange idx size body) m (n*(cost+3)+2) t ∧ I n t := by
  have init := op_addrConst m idx 0 hs (hI 0 _ hi).1
  obtain ⟨t,loop,ht⟩ := loop_invariant_exact (safe := safe) (c := .addrLT idx size)
    (body := .seq body (.op (.incr idx idx))) I (m.putIndex idx 0) n (cost+1) hi
    (by
      intro j hj s hij
      obtain ⟨_,hidx,hsize⟩ := hI j s hij
      obtain ⟨t,run,hnext⟩ := hb j hj s hij
      exact ⟨by simp [Cond.test,hidx,hsize,hj], t.putIndex idx (t.index idx+1),
        run.seq (op_incr t idx idx run.safe_end (hI _ _ hnext).1), hnext⟩)
    (by
      intro t ht
      obtain ⟨safe',hidx,hsize⟩ := hI n t ht
      exact ⟨by simp [Cond.test,hidx,hsize], safe'⟩)
  refine ⟨t, ?_, ht⟩
  have h : Eval safe (.forRange idx size body) m (1+(n*(cost+3)+1)) t := init.seq loop
  rw [show n*(cost+3)+2 = 1+(n*(cost+3)+1) by omega]
  exact h

/-- Row-major Hoare rule. `R` is maintained at row boundaries, `C` at column boundaries.
The callback may update arbitrary working registers and scalar memory. -/
theorem forRowsCols_invariant (row rows col cols N D B : Nat)
    (R : Nat → Memory K → Prop) (C : Nat → Nat → Memory K → Prop) (m : Memory K)
    (hs : safe m) (hi : R 0 (m.putIndex row 0))
    (hR : ∀ r s, R r s → safe s ∧ s.index row = r ∧ s.index rows = N)
    (hstartRow : ∀ r < N, ∀ s, R r s → C r 0 (s.putIndex col 0))
    (hC : ∀ r j s, C r j s → safe s ∧ s.index col = j ∧ s.index cols = D)
    (hcell : ∀ r < N, ∀ j < D, ∀ s, C r j s →
      ∃ t k, k ≤ B ∧ Eval safe body s k t ∧ C r (j+1) (t.putIndex col (t.index col+1)))
    (hendRow : ∀ r < N, ∀ t, C r D t → R (r+1) (t.putIndex row (t.index row+1))) :
    ∃ t k, k ≤ N*(D*(B+3)+5)+2 ∧
      Eval safe (.forRowsCols row rows col cols body) m k t ∧ R N t := by
  apply forRange_invariant row rows N (D*(B+3)+2) R m hs hi hR
  intro r hr s hrow
  obtain ⟨t,k,hk,run,hend⟩ := forRange_invariant col cols D B (C r) s (hR _ _ hrow).1
    (hstartRow r hr s hrow) (hC r) (hcell r hr)
  exact ⟨t,k,hk,run,hendRow r hr t hend⟩

end Block.Eval
end RAM
end LinearProgramming
end Optimization
end OAI
