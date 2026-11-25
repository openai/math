import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.PrimalDual.CopyRAM

/-! Reinitializing the virtual register file between two isolated subroutine calls.
Only odd address registers implement the scan, so clearing address values cannot erase
one of its own pointers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Block Tape

/-- Address register 3 contains zero, 5 the remaining count, and 7 the current even
address. The scalar scan uses zero in scalar register 1. -/
def clearCell (scalars : Bool) : Instr := if scalars then .store 7 1 else .addrStore 7 3

def clearStep (scalars : Bool) : Block :=
  .straight [clearCell scalars, .incr 7 7, .incr 7 7, .decr 5 5]

def clearWindow (scalars : Bool) : Block := .loop (.addrLT 3 5) (clearStep scalars)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private def overwrite (scalars : Bool) (s : Memory K) : Memory K :=
  if scalars then s.putData (s.index 7) 0 else s.putIndex (s.index 7) 0

private theorem overwrite_run (scalars : Bool) (s : Memory K) (hs : Good P s)
    (hzero : s.index 3 = 0) (hz : scalars = true → s.data 1 = 0) :
    Eval (Good P) (.op (clearCell scalars)) s 1 (overwrite scalars s) := by
  cases scalars with
  | false => simpa [clearCell, overwrite, hzero] using
      (Eval.op_addrStore s 7 3 hs (show Good P (s.putIndex (s.index 7) (s.index 3)) from hs))
  | true =>
    have wz : Good P (s.putData (s.index 7) (s.data 1)) := OAI.Optimization.LinearProgramming.PrimalDual.safe_data_write s hs _ _ (hs 1)
    simpa [clearCell, overwrite, hz rfl] using Eval.op_store s 7 1 hs wz

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem overwrite_data (scalars : Bool) (s : Memory K) (j : Nat) :
    (overwrite scalars s).data j = if scalars = true ∧ j=s.index 7 then 0 else s.data j := by
  cases scalars <;> by_cases h : j=s.index 7 <;> simp [overwrite, Memory.putData, Function.update, h]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem overwrite_index (scalars : Bool) (s : Memory K) (j : Nat) :
    (overwrite scalars s).index j = if scalars = false ∧ j=s.index 7 then 0 else s.index j := by
  cases scalars <;> by_cases h : j=s.index 7 <;> simp [overwrite, Memory.putIndex, Function.update, h]

private theorem clearStep_run (scalars : Bool) (s : Memory K) (hs : Good P s)
    (hzero : s.index 3 = 0) (hz : scalars = true → s.data 1 = 0) (j : Nat) (hptr : s.index 7 = 2*j) :
    ∃ t, Eval (Good P) (clearStep scalars) s 4 t ∧
      t.index 7 = 2*(j+1) ∧ t.index 5 = s.index 5-1 ∧
      (∀ a, a ≠ 5 → a ≠ 7 → t.index a =
        if scalars = false ∧ a=2*j then 0 else s.index a) ∧
      ∀ a, t.data a = if scalars = true ∧ a=2*j then 0 else s.data a := by
  let w := overwrite scalars s
  have hw := overwrite_run scalars s hs hzero hz
  have w7 : w.index 7 = 2*j := by rw [overwrite_index, hptr]; simp [show 7 ≠ 2*j by omega]
  have w5 : w.index 5 = s.index 5 := by rw [overwrite_index, hptr]; simp [show 5 ≠ 2*j by omega]
  let a := w.putIndex 7 (2*j+1)
  let b := a.putIndex 7 (2*j+2)
  let t := b.putIndex 5 (s.index 5-1)
  have h1 : Eval (Good P) (.op (.incr 7 7)) w 1 a := by
    simpa only [w7, a] using (eval_incr w hw.safe_end 7 7)
  have h2 : Eval (Good P) (.op (.incr 7 7)) a 1 b := by
    simpa [a,b] using eval_incr a h1.safe_end 7 7
  have h3 : Eval (Good P) (.op (.decr 5 5)) b 1 t := by
    simpa [w5,a,b,t] using eval_decr b h2.safe_end 5 5
  refine ⟨t, hw.seq (h1.seq (h2.seq (h3.seq (.skip h3.safe_end)))), ?_, ?_, ?_, ?_⟩
  · simp [t,b,Nat.mul_add]
  · simp [t]
  · intro i h5 h7
    simp [t,b,a,Memory.putIndex_ne _ h5,Memory.putIndex_ne _ h7,w,overwrite_index,hptr]
  · intro i; simp [t,b,a,w,overwrite_data,hptr]

/-- Identify the addresses erased during the first `n` iterations. -/
def inEvenWindow (lo n i : Nat) : Prop := i % 2 = 0 ∧ 2 * lo ≤ i ∧ i < 2 * (lo + n)

instance (lo n i : Nat) : Decidable (inEvenWindow lo n i) := by unfold inEvenWindow; infer_instance

private theorem evenWindow_succ (lo k i : Nat) :
    inEvenWindow lo (k+1) i ↔ i=2*(lo+k) ∨ inEvenWindow lo k i := by
  unfold inEvenWindow; omega

private structure ClearInv (scalars : Bool) (s : Memory K) (lo n k : Nat) (t : Memory K)
    (P : K → Prop) : Prop where
  good : Good P t
  pointer : t.index 7 = 2*(lo+k)
  remaining : t.index 5 = n-k
  otherIndex : ∀ i, i ≠ 5 → i ≠ 7 → t.index i =
    if scalars = false ∧ inEvenWindow lo k i then 0 else s.index i
  data : ∀ i, t.data i = if scalars = true ∧ inEvenWindow lo k i then 0 else s.data i

/-- Clear a strided window in either the scalar or address bank. This bound counts the
last unsuccessful branch as well as both pointer increments at every iteration. -/
theorem clearWindow_correct (scalars : Bool) (s : Memory K) (lo n : Nat)
    (hs : Good P s) (hz : s.index 3 = 0) (hzero : scalars = true → s.data 1 = 0)
    (hp : s.index 7 = 2*lo) (hn : s.index 5 = n) :
    ∃ t, Eval (Good P) (clearWindow scalars) s (6*n+1) t ∧
      t.index 7=2*(lo+n) ∧ t.index 5=0 ∧
      (∀ i, i≠5 → i≠7 → t.index i = if scalars=false ∧ inEvenWindow lo n i then 0 else s.index i) ∧
      (∀ i, t.data i = if scalars=true ∧ inEvenWindow lo n i then 0 else s.data i) := by
  let I := fun k t => ClearInv scalars s lo n k t P
  have init : I 0 s := by
    refine ⟨hs, by simpa using hp, by simpa using hn, ?_, ?_⟩ <;>
      simp [inEvenWindow]
  have body (k : Nat) (hk : k<n) (t : Memory K) (h : I k t) :
      (Cond.addrLT 3 5).test t = true ∧ ∃ w, Eval (Good P) (clearStep scalars) t 4 w ∧ I (k+1) w := by
    have h3 : t.index 3 = 0 := by rw [h.otherIndex 3 (by decide) (by decide)]; simp [inEvenWindow,hz]
    have h1 : scalars = true → t.data 1 = 0 := by
      intro hb; rw [h.data]; simp [inEvenWindow,hzero hb]
    obtain ⟨w, run, ptr, rem, idx, dat⟩ := clearStep_run scalars t h.good h3 h1 (lo+k) h.pointer
    refine ⟨by simp [Cond.test, h3, h.remaining, Nat.sub_pos_of_lt hk], w, run, run.safe_end, ?_, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc] using ptr
    · rw [rem, h.remaining]; omega
    · intro i h5 h7
      rw [idx i h5 h7, h.otherIndex i h5 h7]
      simp only [evenWindow_succ]
      by_cases eq : i=2*(lo+k) <;> cases scalars <;> simp [eq]
    · intro i
      rw [dat, h.data]
      simp only [evenWindow_succ]
      by_cases eq : i=2*(lo+k) <;> cases scalars <;> simp [eq]
  obtain ⟨t,run,inv⟩ := Eval.loop_invariant_exact I s n 4 init body (fun t h => by
    have h3 : t.index 3 = 0 := by rw [h.otherIndex 3 (by decide) (by decide)]; simp [inEvenWindow,hz]
    exact ⟨by simp [Cond.test,h3,h.remaining], h.good⟩)
  exact ⟨t, by simpa [clearWindow,Nat.mul_comm] using run, inv.pointer,
    by simpa using inv.remaining, inv.otherIndex, inv.data⟩

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
