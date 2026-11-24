import OAI.Computability.VPVNP.LivePublicExpr
import OAI.Computability.VPVNP.RAMTapeISAComparison
import OAI.Computability.VPVNP.RAMTapeWordISAStage

/-! # Physical word operations for the length-only public expressions

All arithmetic uses the fixed RAM word kernels. Natural subtraction tests
the unsigned order first, since the expression language truncates at zero.
Powers of two shift a literal unit and constant division uses the physical
word divider.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicExprMachine

open BurstRAM PrivateRAM LiveProgram

/-- Represent a natural number as a word by reduction modulo two to the word width. -/
abbrev packed (w n : ℕ) : Word w := Fin.ofNat (2^w) n

/-- The four geometry inputs in register order, namely input length, site address width, bucket
capacity, and RAM word width. -/
def geometryNat (g : Geometry) : Fin 4 → ℕ := ![g.n, g.d, g.H, g.w]

/-- Encode the selected geometry parameter at the RAM word width. -/
def geometryWords (g : Geometry) (i : Fin 4) : Word g.w := packed g.w (geometryNat g i)

theorem packed_val {w n : ℕ} (h : n < 2^w) : (packed w n).val = n := Nat.mod_eq_of_lt h

variable {r k w : ℕ}

/-- Copy one geometry word into an arithmetic register. -/
def load (dst : Fin r) (i : Fin k) : FiniteRoutine (ISA.Port r k) :=
  ISA.loadOperand (.pub i) (.reg dst)

theorem load_runs (dst : Fin r) (i : Fin k) (pub : Fin k → Word w) (persist : Word w)
    (rs : Fin r → Word w) (log : WriteLog w) :
    (load dst i).Runs (8*w+3) (ISA.bank pub persist rs log)
      (ISA.bank pub persist (Function.update rs dst (pub i)) log) := by
  let s := ISA.bank pub persist rs log
  have hr := ISA.loadOperand_runs (src := ISA.Port.pub i) (dst := .reg dst) (by simp)
    (by simp [ISA.copySafe]) (by simp [ISA.copySafe]) s rfl rfl
  change (load dst i).Runs ((wordBits (rs dst)).length + 7*(wordBits (pub i)).length+3)
    s (Function.update s (.reg dst) (wordBits (pub i))) at hr
  simpa only [length_wordBits, s, ISA.bank_updateReg, show w+7*w+3=8*w+3 by omega] using hr

/-- Compare unsigned operands and return zero on underflow, otherwise compute their word
difference. -/
def subtract (dst a b : Fin r) : FiniteRoutine (ISA.Port r k) :=
  (ISA.compareRegs .lt a b).followedBy (.ofRoutine (Routine.popCase (.work 0) (Routine.halt false)
    (ISA.binary .sub dst a b).body (ISA.loadLiteral 0 dst).body))

theorem subtract_runs (dst a b : Fin r) (pub : Fin k → Word w) (persist : Word w)
    (rs : Fin r → Word w) (log : WriteLog w) :
    ∃ t ≤ 150*(w+1)^2, (subtract dst a b).Runs t (ISA.bank pub persist rs log)
      (ISA.bank pub persist (Function.update rs dst (packed w ((rs a).val-(rs b).val))) log) := by
  let s := ISA.bank pub persist rs log
  have cmp := ISA.compareRegs_run .lt a b pub persist rs log
  let branch := Routine.popCase (ISA.Port.work 0) (Routine.halt false)
    (ISA.binary (k := k) .sub dst a b).body (ISA.loadLiteral 0 dst).body
  have back (bit : Bool) : Function.update (Function.update s (.work 0) [bit]) (.work 0) [] = s := by
    rw [Function.update_idem]
    exact Function.update_eq_self ..
  by_cases h : (rs a).val < (rs b).val
  · have hb : TapeWord.Comparison.Op.lt.eval (rs a) (rs b) = true := decide_eq_true h
    rw [hb] at cmp
    have val : (rs a).val - (rs b).val = 0 := Nat.sub_eq_zero_of_le h.le
    rw [val]
    have put := ISA.loadLiteral_run 0 dst pub persist rs log
    have select : branch.Runs ((8*w+3)+1) (Function.update s (.work 0) [true]) _ :=
      Routine.runs_popCase_true _ _ _ _ (Function.update_self ..) (by rw [back]; exact put)
    refine ⟨_, ?_, FiniteRoutine.Runs.followedBy cmp (b := .ofRoutine branch) select⟩
    nlinarith [Nat.zero_le (w*w)]
  · have hb : TapeWord.Comparison.Op.lt.eval (rs a) (rs b) = false := decide_eq_false h
    rw [hb] at cmp
    obtain ⟨u, hu, hr⟩ := ISA.binary_runs .sub dst a b pub persist rs log
    have he : BinaryOp.sub.eval (rs a) (rs b) = packed w ((rs a).val-(rs b).val) := by
      apply Fin.ext
      change ((2^w - (rs b).val + (rs a).val) % 2^w) = _
      have hlt := (rs b).isLt
      have hadd : 2^w - (rs b).val + (rs a).val = ((rs a).val-(rs b).val)+2^w := by omega
      rw [hadd, Nat.add_mod_right]
      rfl
    rw [he] at hr
    have select : branch.Runs (u+1) (Function.update s (.work 0) [false]) _ :=
      Routine.runs_popCase_false _ _ _ _ (Function.update_self ..) (by rw [back]; exact hr)
    refine ⟨_, ?_, FiniteRoutine.Runs.followedBy cmp (b := .ofRoutine branch) select⟩
    nlinarith [Nat.zero_le (w*w)]

/-- Binary operations of the public expression language, namely addition, truncated
subtraction, and multiplication. -/
inductive Arithmetic where | add | sub | mul
  deriving DecidableEq

/-- Interpret the binary operation on natural numbers, with subtraction truncated at zero. -/
def Arithmetic.eval : Arithmetic → ℕ → ℕ → ℕ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Compile the binary operation to a word routine, using an unsigned comparison for truncated
subtraction. -/
def Arithmetic.code (op : Arithmetic) (dst a b : Fin r) : FiniteRoutine (ISA.Port r k) :=
  match op with
  | .add => ISA.binary .add dst a b
  | .sub => subtract dst a b
  | .mul => ISA.binary .mul dst a b

theorem Arithmetic.runs (op : Arithmetic) (dst a b : Fin r) (pub : Fin k → Word w)
    (persist : Word w) (rs : Fin r → Word w) (log : WriteLog w) :
    ∃ t ≤ 150*(w+1)^2, (op.code dst a b).Runs t (ISA.bank pub persist rs log)
      (ISA.bank pub persist (Function.update rs dst (packed w (op.eval (rs a).val (rs b).val))) log) := by
  cases op with
  | add =>
    obtain ⟨t, ht, hr⟩ := ISA.binary_runs .add dst a b pub persist rs log
    exact ⟨t, ht.trans (Nat.mul_le_mul_right _ (by decide)), hr⟩
  | sub => exact subtract_runs ..
  | mul =>
    obtain ⟨t, ht, hr⟩ := ISA.binary_runs .mul dst a b pub persist rs log
    exact ⟨t, ht.trans (Nat.mul_le_mul_right _ (by decide)), hr⟩

/-- Unary public-expression operations that need an auxiliary literal, namely division by a
fixed natural and raising two to a power. -/
inductive ConstantOp where
  | divConst (denominator : ℕ)
  | pow2

/-- The auxiliary literal loaded for a constant operation, either its divisor or the unit to
shift left. -/
def ConstantOp.literal : ConstantOp → ℕ
  | .divConst b => b
  | .pow2 => 1

/-- Interpret the fixed-divisor or power-of-two operation on a natural input. -/
def ConstantOp.eval : ConstantOp → ℕ → ℕ
  | .divConst b => (· / b)
  | .pow2 => (2^·)

/-- Load the auxiliary literal, then divide the destination word or shift a unit left by its
value. -/
def ConstantOp.code (op : ConstantOp) (dst tmp : Fin r) : FiniteRoutine (ISA.Port r k) :=
  (ISA.loadLiteral op.literal tmp).followedBy (match op with
    | .divConst _ => ISA.binary .div dst dst tmp
    | .pow2 => ISA.binary .shiftLeft dst tmp dst)

theorem ConstantOp.runs (op : ConstantOp) (dst tmp : Fin r) (hne : dst ≠ tmp)
    (pub : Fin k → Word w) (persist : Word w) (rs : Fin r → Word w) (log : WriteLog w)
    (hlit : op.literal < 2^w) (hout : op.eval (rs dst).val < 2^w) :
    ∃ t ≤ 150*(w+1)^2, (op.code dst tmp).Runs t (ISA.bank pub persist rs log)
      (ISA.bank pub persist (Function.update (Function.update rs tmp (packed w op.literal))
        dst (packed w (op.eval (rs dst).val))) log) := by
  let mid := Function.update rs tmp (packed w op.literal)
  have load := ISA.loadLiteral_run op.literal tmp pub persist rs log
  have htmp : (mid tmp).val = op.literal := by simp only [mid, Function.update_self, packed_val hlit]
  have hdst : mid dst = rs dst := Function.update_of_ne hne ..
  cases op with
  | divConst b =>
    obtain ⟨u, hu, hr⟩ := ISA.binary_runs .div dst dst tmp pub persist mid log
    have he : BinaryOp.div.eval (mid dst) (mid tmp) = packed w ((rs dst).val / b) := by
      simp only [BinaryOp.eval, hdst, htmp, ConstantOp.literal, packed]
    rw [he] at hr
    exact ⟨_, by nlinarith [Nat.zero_le (w*w)], FiniteRoutine.Runs.followedBy load hr⟩
  | pow2 =>
    have hexp : (rs dst).val < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hout
    obtain ⟨u, hu, hr⟩ := ISA.binary_runs .shiftLeft dst tmp dst pub persist mid log
    have he : BinaryOp.shiftLeft.eval (mid tmp) (mid dst) = packed w (2^(rs dst).val) := by
      simp only [BinaryOp.eval, hdst, hexp, ↓reduceIte, htmp, ConstantOp.literal, Nat.shiftLeft_eq,
        Nat.one_mul, packed]
    rw [he] at hr
    exact ⟨_, by nlinarith [Nat.zero_le (w*w)], FiniteRoutine.Runs.followedBy load hr⟩

end RAMTape.PublicExprMachine

end VPVNP
end Computability
end OAI
