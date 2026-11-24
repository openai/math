import OAI.Computability.VPVNP.LiveProgramPieces
import Mathlib.Data.ZMod.Defs
import OAI.Computability.VPVNP.PrimedCounterRenameRun
import OAI.Computability.VPVNP.RAMTapePublicInputOperands

/-!
# Native register computation of the compressed pair's static operands

The first twelve registers belong to the geometry and logarithm kernels.
Expression registers follow those registers in increasing order. Computing
a right operand one register higher leaves the left operand available for
the arithmetic instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeOperands
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM LiveProgram
open scoped Fin.CommRing

/-- Size of the operand register bank, with twelve fixed registers followed by temporary slots
numbered from zero through `r`. -/
abbrev registerCount (r : ℕ) := 12+(r+1)
/-- Native operand flows with temporary slots up to `r` and access to the eleven public
pair-stage words. -/
abbrev Code (r : ℕ) := Flow (registerCount r) 11

/-- Locate a geometry or logarithm register at the same index in the enlarged operand bank. -/
def fixed (r : ℕ) (i : Fin 12) : Fin (registerCount r) := i.castAdd (r+1)

/-- The injective register map used to lift executions of twelve-register routines into the
native operand bank. -/
def fixedEmbedding (r : ℕ) : Fin 12 ↪ Fin (registerCount r) :=
  ⟨fixed r,fun _ _ h => Fin.ext (congrArg (fun j : Fin (registerCount r) => j.val) h)⟩

/-- Locate a temporary operand register after the twelve fixed registers, reducing the slot
index modulo `r+1`. -/
def temp (r base : ℕ) : Fin (registerCount r) := (Fin.ofNat (r+1) base).natAdd 12

theorem temp_val {r base : ℕ} (h : base ≤ r) : (temp r base).val = 12+base := by
  change 12+base%(r+1) = _
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The six input words shared with the tape operand evaluator, encoding length, address width,
bucket size, word width, prefix length and packed prefix value. -/
def words (g : Geometry) (lit : LiteralPrefix) : Fin 6 → Word g.w :=
  RAMTape.InputOperandMachine.input g lit

/-- Register assignment for the six operand inputs in logical order. The bucket precedes the
word width in that order and occupies register 7. -/
def inputSlot : Fin 6 → Fin 12 := ![4,5,7,6,8,9]

/-- Locate the fixed register holding logical input `i` in an operand bank with temporary slots
up to `r`. -/
abbrev inputReg (r : ℕ) (i : Fin 6) := fixed r (inputSlot i)

/-- The six designated registers already contain the encoded geometry and prefix words required
by operand evaluation. -/
def Ready (g : Geometry) (lit : LiteralPrefix) {r : ℕ} (rs : Regs g.w (registerCount r)) : Prop :=
  ∀ i : Fin 6, rs (inputReg r i) = words g lit i

/-- The output agrees with the input on registers from 4 up to but excluding `12+base`,
protecting the fixed inputs and all earlier temporary results. -/
def Keeps {r w : ℕ} (base : ℕ) (rs out : Regs w (registerCount r)) : Prop :=
  ∀ i, 4 ≤ i.val → i.val < 12+base → out i = rs i

theorem Keeps.ready {g : Geometry} {lit : LiteralPrefix} {r base : ℕ}
    {rs out : Regs g.w (registerCount r)} (h : Keeps base rs out) (hr : Ready g lit rs) :
    Ready g lit out := by
  intro i
  have hi : 4 ≤ (inputSlot i).val := by fin_cases i <;> decide
  have hlt := (inputSlot i).isLt
  exact (h _ hi (show (inputSlot i).val < 12+base by omega)).trans (hr i)

/-- From any ready bank the code produces the word for `v` in temporary slot `base` within the
tick budget, preserves the protected registers and returns the original memory. -/
def Eval (g : Geometry) (lit : LiteralPrefix) (r base v steps : ℕ) (code : Code r) : Prop :=
  ∀ (pub : Fin 11 → Word g.w) (state : Word g.w) (m : Memory g.w) (rs : Regs g.w (registerCount r)),
    Ready g lit rs → ∃ t ≤ steps, ∃ out : Regs g.w (registerCount r),
      Flow.Exec pub state code rs m (List.replicate t .tick) out m ∧
      out (temp r base) = Fin.ofNat _ v ∧ Keeps base rs out

theorem seqTicks {w r k : ℕ} {pub : Fin k → Word w} {state : Word w} {m : Memory w}
    {a b : Flow r k} {rs mid out : Regs w r} {j t : ℕ}
    (ha : Flow.Exec pub state a rs m (List.replicate j .tick) mid m)
    (hb : Flow.Exec pub state b mid m (List.replicate t .tick) out m) :
    Flow.Exec pub state (.seq a b) rs m (List.replicate (j+t) .tick) out m := by
  simpa only [List.replicate_add] using ha.seq hb

theorem update_keep {r w base : ℕ} (hb : base ≤ r) (rs : Regs w (registerCount r))
    (v : Word w) : Keeps base rs (Function.update rs (temp r base) v) := by
  intro i _ hi
  exact Function.update_of_ne (fun h => by rw [h,temp_val hb] at hi; omega) ..

theorem scratch_keep {r w base : ℕ} (rs : Regs w (registerCount r)) (j : Fin 12)
    (hj : j.val < 4) (v : Word w) : Keeps base rs (Function.update rs (fixed r j) v) := by
  intro i hi _
  have he : (fixed r j).val = j.val := rfl
  exact Function.update_of_ne (fun h => by rw [h,he] at hi; omega) ..

theorem Keeps.trans {r w b : ℕ} {rs mid out : Regs w (registerCount r)}
    (h : Keeps b rs mid) (k : Keeps b mid out) : Keeps b rs out :=
  fun i lo hi => (k i lo hi).trans (h i lo hi)

theorem Keeps.mono {r w a b : ℕ} {rs out : Regs w (registerCount r)} (h : Keeps b rs out) (hab : a ≤ b) :
    Keeps a rs out := fun i lo hi => h i lo (by omega)

private def addUnits {r : ℕ} (dst : Fin (registerCount r)) : ℕ → Code r
  | 0 => .line (.constant dst 0)
  | n+1 => .seq (addUnits dst n) (.line (.binary .add dst dst (fixed r 0)))

/-- Build the literal `n` in the destination register by loading one into scratch register 0
and adding that unit `n` times from zero. -/
def literal {r : ℕ} (dst : Fin (registerCount r)) (n : ℕ) : Code r :=
  .seq (.line (.constant (fixed r 0) 1)) (addUnits dst n)

private theorem addUnits_run {w r : ℕ} (pub : Fin 11 → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w (registerCount r)) (dst : Fin (registerCount r)) (hd : dst ≠ fixed r 0)
    (h1 : rs (fixed r 0) = 1) (n : ℕ) :
    Flow.Exec pub state (addUnits dst n) rs m (List.replicate (n+1) .tick)
      (Function.update rs dst (Fin.ofNat _ n)) m := by
  induction n with
  | zero => exact Flow.Exec.line rfl
  | succ n ih =>
    let mid := Function.update rs dst (Fin.ofNat (2^w) n)
    have hv : mid (fixed r 0) = 1 := (Function.update_of_ne hd.symm ..).trans h1
    have hop : Flow.Exec pub state (.line (.binary .add dst dst (fixed r 0))) mid m [.tick]
        (Function.update rs dst (Fin.ofNat _ (n+1))) m := by
      apply Flow.Exec.line
      simp only [Op.effect,BinaryOp.eval,hv,mid,Function.update_self,Function.update_idem]
      rw [show Fin.ofNat (2^w) n + 1 = Fin.ofNat (2^w) (n+1) from (Nat.cast_succ (R := Word w) n).symm]
    exact seqTicks (t := 1) ih hop

theorem literal_run {w r : ℕ} (pub : Fin 11 → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w (registerCount r)) (dst : Fin (registerCount r)) (hd : dst ≠ fixed r 0) (n : ℕ) :
    let mid := Function.update rs (fixed r 0) (Fin.ofNat (2^w) 1)
    Flow.Exec pub state (literal dst n) rs m (List.replicate (n+2) .tick)
      (Function.update mid dst (Fin.ofNat _ n)) m := by
  let mid := Function.update rs (fixed r 0) (Fin.ofNat (2^w) 1)
  have one : Flow.Exec pub state (.line (.constant (fixed r 0) 1)) rs m [.tick] mid m := .line rfl
  have h := addUnits_run pub state m mid dst hd (Function.update_self ..) n
  simpa only [literal, show 1+(n+1)=n+2 by omega] using seqTicks (j := 1) one h

theorem temp_ne_fixed {r : ℕ} (base : ℕ) (i : Fin 12) : temp r base ≠ fixed r i := by
  intro h
  have e := congrArg Fin.val h
  change 12+(base%(r+1)) = i.val at e
  omega

theorem literal_eval (g : Geometry) (lit : LiteralPrefix) {r base : ℕ} (hb : base ≤ r) (v : ℕ) :
    Eval g lit r base v (v+2) (literal (temp r base) v) := by
  intro pub st m rs _
  let mid := Function.update rs (fixed r 0) (Fin.ofNat (2^g.w) 1)
  exact ⟨_,le_rfl,_,literal_run pub st m rs (temp r base) (temp_ne_fixed base 0) v,Function.update_self ..,
    (scratch_keep rs 0 (by decide) _).trans (update_keep hb mid _)⟩

theorem input_eval (g : Geometry) (lit : LiteralPrefix) {r base : ℕ} (hb : base ≤ r) (i : Fin 6)
    (v : ℕ) (hv : words g lit i = Fin.ofNat _ v) :
    Eval g lit r base v 1 (.line (.copy (temp r base) (inputReg r i))) := by
  intro pub st m rs hr
  let out := Function.update rs (temp r base) (rs (inputReg r i))
  exact ⟨1,le_rfl,out,.line rfl,(Function.update_self ..).trans ((hr i).trans hv),update_keep hb rs _⟩

end PairSimulation.NativeOperands

end VPVNP
end Computability
end OAI
