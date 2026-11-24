import OAI.Computability.VPVNP.RAMTapeISAPrepare
import OAI.Computability.VPVNP.RankQueryStackDispatch

/-!
# Fixed bit-stack routines for register decision trees

Arithmetic instructions stage their two word operands before writeback. The
natural subtraction instruction tests for underflow and returns zero in that
case. Decisions compare two registers on the tape and execute one statically
specified branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Dispatch

open BurstRAM PrivateRAM RAMTape TapeWord

variable {w r : ℕ}

/-- Contents of `r` registers holding words of width `w`. -/
abbrev Regs (r w : ℕ) := Fin r → Word w
/-- A bit-stack routine on `r` register ports with no public input words. -/
abbrev Machine (r : ℕ) := FiniteRoutine (ISA.Port r 0)

/-- Translate a natural-arithmetic instruction to the corresponding binary word opcode. -/
def Arith.opcode : Arith → BinaryOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod

/-- Width-bounded register semantics for natural operations. -/
def Arith.word (a : Arith) (x y : Word w) : Word w :=
  if a = .sub ∧ x < y then 0 else a.opcode.eval x y

theorem Arith.word_val (a : Arith) (x y : Word w) (h : a.eval x.val y.val < 2^w) :
    (a.word x y).val = a.eval x.val y.val := by
  cases a with
  | sub =>
    by_cases hs : x < y
    · have hv : x.val < y.val := hs
      simp [word, hs, Arith.eval, Nat.sub_eq_zero_of_le hv.le]
    · have hv : y ≤ x := le_of_not_gt hs
      simp [word, hs, opcode, BinaryOp.eval, Fin.sub_val_of_le hv, Arith.eval]
  | add | mul | div | mod =>
    simp [word, opcode, BinaryOp.eval, Fin.val_add, Fin.val_mul, Arith.eval]
    exact Nat.mod_eq_of_lt h

/-- Register programs built from literals, copies, arithmetic, sequencing, and equality tests. -/
inductive RegCode (r : ℕ) where
  | ret
  | lit (dst : Fin r) (n : ℕ)
  | copy (dst src : Fin r)
  | op (dst : Fin r) (a : Arith) (x y : Fin r)
  | seq (first second : RegCode r)
  | test (x y : Fin r) (yes no : RegCode r)

namespace RegCode

/-- Execute a register program on width-`w` words, saturating subtraction at zero. -/
def exec : RegCode r → Regs r w → Regs r w
  | .ret, rs => rs
  | .lit dst n, rs => Function.update rs dst (Fin.ofNat _ n)
  | .copy dst src, rs => Function.update rs dst (rs src)
  | .op dst a x y, rs => Function.update rs dst (a.word (rs x) (rs y))
  | .seq l r, rs => r.exec (l.exec rs)
  | .test x y yes no, rs => if rs x = rs y then yes.exec rs else no.exec rs

/-- Weighted instruction count used to bound execution time, charging two units for arithmetic
and the longer arm of a test. -/
def length : RegCode r → ℕ
  | .ret | .lit .. | .copy .. => 1
  | .op .. => 2
  | .seq l r => l.length + r.length
  | .test _ _ yes no => 1 + max yes.length no.length

private def ifTest (op : Comparison.Op) (x y : Fin r) (yes no : Machine r) : Machine r :=
  (ISA.compareRegs op x y).followedBy (FiniteRoutine.ofRoutine
    (Routine.popCase (.work 0) Routine.ret no.body yes.body))

/-- Compile a register program into a bit-stack routine, testing for underflow before a
subtraction. -/
def compile : RegCode r → Machine r
  | .ret => FiniteRoutine.ret
  | .lit dst n => ISA.loadLiteral n dst
  | .copy dst src => ISA.prepare (Instr.copy (w := 1) (p := 1) dst src 0)
  | .op dst .sub x y => ifTest .lt x y (ISA.loadLiteral 0 dst) (ISA.binary .sub dst x y)
  | .op dst a x y => ISA.binary a.opcode dst x y
  | .seq l r => l.compile.followedBy r.compile
  | .test x y yes no => ifTest .eq x y yes.compile no.compile

private theorem ifTest_runs (op : Comparison.Op) (x y : Fin r) (yes no : Machine r)
    (pub : Fin 0 → Word w) (persistent : Word w) (rs out : Regs r w) (t : ℕ)
    (hb : (if op.eval (rs x) (rs y) then yes else no).Runs t
      (ISA.bank pub persistent rs []) (ISA.bank pub persistent out [])) :
    (ifTest op x y yes no).Runs (20*w+10 + (t+1))
      (ISA.bank pub persistent rs []) (ISA.bank pub persistent out []) := by
  let s := ISA.bank pub persistent rs []
  let b := op.eval (rs x) (rs y)
  have hb' : (if b then yes else no).Runs t s (ISA.bank pub persistent out []) := hb
  have hc := ISA.compareRegs_run op x y pub persistent rs []
  have hu : Function.update (Function.update s (.work 0) [b]) (.work 0) [] = s := by
    rw [Function.update_idem]; exact Function.update_eq_self ..
  apply FiniteRoutine.Runs.followedBy hc
  change (Routine.popCase (.work 0) Routine.ret no.body yes.body).Runs (t+1)
    (Function.update s (.work 0) [b]) (ISA.bank pub persistent out [])
  cases h : b with
  | false =>
    apply Routine.runs_popCase_false (tail := []) (hs := Function.update_self ..)
    rw [← h, hu]
    simpa [h] using hb'
  | true =>
    apply Routine.runs_popCase_true (tail := []) (hs := Function.update_self ..)
    rw [← h, hu]
    simpa [h] using hb'

/-- The compiled program is finite and independent of the operand width.
It returns the specified register bank within a quadratic per-instruction
bit-stack clock. -/
theorem compile_runs (c : RegCode r) (pub : Fin 0 → Word w) (persistent : Word w) (rs : Regs r w) :
    ∃ t ≤ c.length * (100*(w+1)^2), c.compile.Runs t (ISA.bank pub persistent rs [])
      (ISA.bank pub persistent (c.exec rs) []) := by
  have hc : 20*w+11 ≤ 100*(w+1)^2 := by nlinarith [Nat.zero_le (w^2)]
  induction c generalizing rs with
  | ret => exact ⟨1, by change 1 ≤ 1 * _; omega, Routine.runs_ret _⟩
  | lit dst n => exact ⟨8*w+3, by change _ ≤ 1 * _; omega, ISA.loadLiteral_run ..⟩
  | copy dst src =>
    let ins : Instr 1 1 r 0 := .copy dst src 0
    let cfg : LogConfig w 1 r := ⟨0,persistent,rs,[]⟩
    obtain ⟨t,ht,hr⟩ := ISA.prepare_runs ins pub cfg
    exact ⟨t, by simpa [length, ISA.prepareBound, cfg] using ht, hr⟩
  | op dst a x y =>
    cases a with
    | add | mul | div | mod =>
      obtain ⟨t,ht,hr⟩ := ISA.binary_runs _ dst x y pub persistent rs []
      exact ⟨t, by change _ ≤ 2 * _; omega, hr⟩
    | sub =>
      cases h : Comparison.Op.lt.eval (rs x) (rs y) with
      | false =>
        have hn : ¬rs x < rs y := by simpa [Comparison.Op.eval] using h
        obtain ⟨t,ht,hr⟩ := ISA.binary_runs BinaryOp.sub dst x y pub persistent rs []
        have hrun := ifTest_runs .lt x y (ISA.loadLiteral 0 dst) (ISA.binary .sub dst x y) pub persistent rs _ t
          (by simpa [h] using hr)
        exact ⟨20*w+10+(t+1), by change _ ≤ 2 * _; omega, by simpa [exec, compile, Arith.word, hn, Arith.opcode] using hrun⟩
      | true =>
        have hy : rs x < rs y := by simpa [Comparison.Op.eval] using h
        have hr := ISA.loadLiteral_run 0 dst pub persistent rs []
        have hrun := ifTest_runs .lt x y (ISA.loadLiteral 0 dst) (ISA.binary .sub dst x y) pub persistent rs _ _
          (by simpa [h] using hr)
        exact ⟨20*w+10+(8*w+3+1), by change _ ≤ 2 * _; omega, by simpa [exec, compile, Arith.word, hy] using hrun⟩
  | seq l r ihl ihr =>
    obtain ⟨a,ha,hl⟩ := ihl rs
    obtain ⟨b,hb,hr⟩ := ihr (l.exec rs)
    exact ⟨a+b, by simpa [length, Nat.add_mul] using Nat.add_le_add ha hb, hl.followedBy hr⟩
  | test x y yes no ihy ihn =>
    by_cases he : rs x = rs y
    · have hf : Comparison.Op.eq.eval (rs x) (rs y) = true := by simp [Comparison.Op.eval, he]
      obtain ⟨t,ht,hr⟩ := ihy rs
      have hrun := ifTest_runs .eq x y yes.compile no.compile pub persistent rs _ _ (by simpa [hf] using hr)
      refine ⟨_, ?_, by simpa [compile, exec, he] using hrun⟩
      have hm := Nat.mul_le_mul_right (100*(w+1)^2) (Nat.le_max_left yes.length no.length)
      simp only [length, Nat.add_mul, Nat.one_mul]
      omega
    · have hf : Comparison.Op.eq.eval (rs x) (rs y) = false := by simp [Comparison.Op.eval, he]
      obtain ⟨t,ht,hr⟩ := ihn rs
      have hrun := ifTest_runs .eq x y yes.compile no.compile pub persistent rs _ _ (by simpa [hf] using hr)
      refine ⟨_, ?_, by simpa [compile, exec, he] using hrun⟩
      have hm := Nat.mul_le_mul_right (100*(w+1)^2) (Nat.le_max_right yes.length no.length)
      simp only [length, Nat.add_mul, Nat.one_mul]
      omega

end RegCode

end RankQuery.Stack.Dispatch

end VPVNP
end Computability
end OAI
