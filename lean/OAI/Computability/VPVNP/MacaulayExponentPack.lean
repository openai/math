import OAI.Computability.VPVNP.MacaulayExponentQuery
import OAI.Computability.VPVNP.RoutineSpace
import OAI.Computability.VPVNP.RankQueryStackRegister
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.SliceArithmeticLoop

/-!
# Packing the exponent input of a scalar equation-coefficient query

One step per variable extracts a pair of radix digits, checks the monomial
divisibility condition, and prepends the little-endian word of their
truncated difference. Processing the low radix digits first leaves the
exponents on the output stack in the original variable order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.ExponentPack

open RAMTape BurstRAM RankQuery.Stack.Dispatch

/-- Stacks for the unary variable counter, the packed residual exponents and the temporary
word-copy buffer. -/
inductive Streams where
  | marker | packed | scratch
  deriving DecidableEq

instance : Fintype Streams := ⟨{.marker, .packed, .scratch}, fun s => by cases s <;> decide⟩

/-- Stack addresses of the ten-register subtraction routine and its three auxiliary streams. -/
abbrev Port := RAMTape.ISA.Port 10 0 ⊕ Streams

/-- Registers zero and one store the radices, two and three the residual
source and column, four the divisibility flag, five through eight the
arithmetic scratch, and nine a zero word. -/
def arithmetic : RegCode 10 :=
  .seq (.op 5 .mod 2 0) <| .seq (.op 6 .mod 3 1) <| .seq (.op 7 .sub 6 5) <|
  .seq (.op 8 .sub 5 6) <| .seq (.test 8 9 .ret (.lit 4 0)) <|
  .seq (.op 2 .div 2 0) (.op 3 .div 3 1)

/-- Prepend a copy of the current residual exponent word from register seven to the packed
output stack. -/
def emit : FiniteRoutine Port := SuccessorFields.prependCopy (.inl (.reg 7)) (.inr .packed) (.inr .scratch)

/-- Read one pair of radix digits, update the divisibility flag, and prepend their truncated
difference to the output. -/
def body : FiniteRoutine Port := (arithmetic.compile.onPorts Sum.inl).followedBy emit

/-- Repeat the residual-exponent body once for each marker on the variable counter. -/
def machine : FiniteRoutine Port := FiniteRoutine.repeatMarked (.inr .marker) body

/-- Register stacks with n remaining variable markers, the current packed output and empty copy
scratch. -/
def frame {w : ℕ} (reg : Regs 10 w) (n : ℕ) (out : List Bool) : Stacks Port :=
  Sum.elim (RAMTape.ISA.bank Fin.elim0 0 reg []) fun
    | .marker => List.replicate n true
    | .packed => out
    | .scratch => []

private theorem frame_pop {w : ℕ} (reg : Regs 10 w) (n : ℕ) (out : List Bool) :
    Function.update (frame reg (n+1) out) (.inr .marker) (List.replicate n true) = frame reg n out := by
  funext j; rcases j with j | j
  · simp [frame]
  · cases j <;> rfl

private theorem frame_prepend {w : ℕ} (reg : Regs 10 w) (n : ℕ) (out : List Bool) :
    Function.update (frame reg n out) (.inr .packed) (wordBits (reg 7) ++ out) =
      frame reg n (wordBits (reg 7) ++ out) := by
  funext j; rcases j with j | j
  · simp [frame]
  · cases j <;> rfl

/-- Tick bound for one digit comparison and one residual-word copy at register width w. -/
def bodyCost (w : ℕ) := arithmetic.length * (100*(w+1)^2) + (5*w+2)

theorem body_run {w : ℕ} (reg : Regs 10 w) (n : ℕ) (out : List Bool) :
    ∃ steps ≤ bodyCost w, body.Runs steps (frame reg n out)
      (frame (arithmetic.exec reg) n (wordBits (arithmetic.exec reg 7) ++ out)) := by
  obtain ⟨k,hk,hstep⟩ := arithmetic.compile_runs Fin.elim0 0 reg
  have hreg : (arithmetic.compile.onPorts (Sum.inl : RAMTape.ISA.Port 10 0 → Port)).Runs k
      (frame reg n out) (frame (arithmetic.exec reg) n out) := by
    apply arithmetic.compile.runs_onPorts_framed Sum.inl_injective hstep (fun _ => rfl) (fun _ => rfl)
    rintro (i | i) hi
    · exact (hi i rfl).elim
    · rfl
  let R := arithmetic.exec reg
  have hc := SuccessorFields.prependCopy_runs (K := Port) (.inl (.reg 7)) (.inr .packed) (.inr .scratch)
    (by decide) (by decide) (by decide) (frame R n out) rfl
  change emit.Runs (5*(wordBits (R 7)).length+2) (frame R n out)
    (Function.update _ (.inr .packed) (wordBits (R 7) ++ out)) at hc
  rw [length_wordBits, frame_prepend] at hc
  exact ⟨_, Nat.add_le_add_right hk _, hreg.followedBy hc⟩

/-- Representation of the live registers at a variable boundary. -/
structure Holds {w : ℕ} (reg : Regs 10 w) (A B a b : ℕ) (good : Bool) : Prop where
  srcBase : reg 0 = ISA.word w A
  colBase : reg 1 = ISA.word w B
  src : reg 2 = ISA.word w a
  col : reg 3 = ISA.word w b
  flag : reg 4 = ISA.word w good.toNat
  zero : reg 9 = ISA.word w 0

private theorem arith_word {w x y : ℕ} (op : Arith) (hx : x < 2^w) (hy : y < 2^w)
    (hz : op.eval x y < 2^w) :
    op.word (ISA.word w x) (ISA.word w y) = ISA.word w (op.eval x y) := by
  have hxy (a : ℕ) (ha : a < 2^w) : (ISA.word w a).val = a := Nat.mod_eq_of_lt ha
  apply Fin.ext
  rw [hxy _ hz]
  simpa only [hxy x hx, hxy y hy] using op.word_val (ISA.word w x) (ISA.word w y) (by
    rwa [hxy x hx, hxy y hy])

private theorem step_values {w A B a b : ℕ} {good : Bool} {reg : Regs 10 w} (h : Holds reg A B a b good)
    (hA : A < 2^w) (hB : B < 2^w) (ha : a < 2^w) (hb : b < 2^w) :
    let R := arithmetic.exec reg
    Holds R A B (a/A) (b/B) (good && decide (a%A ≤ b%B)) ∧
      R 7 = ISA.word w (b%B-a%A) := by
  have h₁ : Arith.mod.word (reg 2) (reg 0) = ISA.word w (a%A) := by
    rw [h.src, h.srcBase]; exact arith_word _ ha hA ((Nat.mod_le ..).trans_lt ha)
  have h₂ : Arith.mod.word (reg 3) (reg 1) = ISA.word w (b%B) := by
    rw [h.col, h.colBase]; exact arith_word _ hb hB ((Nat.mod_le ..).trans_lt hb)
  have h₃ := arith_word .sub ((Nat.mod_le b B).trans_lt hb) ((Nat.mod_le a A).trans_lt ha)
    ((Nat.sub_le (b%B) (a%A)).trans_lt ((Nat.mod_le ..).trans_lt hb))
  have h₄ := arith_word .sub ((Nat.mod_le a A).trans_lt ha) ((Nat.mod_le b B).trans_lt hb)
    ((Nat.sub_le (a%A) (b%B)).trans_lt ((Nat.mod_le ..).trans_lt ha))
  have h₅ : Arith.div.word (reg 2) (reg 0) = ISA.word w (a/A) := by
    rw [h.src, h.srcBase]; exact arith_word _ ha hA ((Nat.div_le_self ..).trans_lt ha)
  have h₆ : Arith.div.word (reg 3) (reg 1) = ISA.word w (b/B) := by
    rw [h.col, h.colBase]; exact arith_word _ hb hB ((Nat.div_le_self ..).trans_lt hb)
  change Arith.sub.word _ _ = ISA.word w (b%B-a%A) at h₃
  change Arith.sub.word _ _ = ISA.word w (a%A-b%B) at h₄
  have hword := ISA.word_eq ((Nat.sub_le (a%A) (b%B)).trans_lt ((Nat.mod_le ..).trans_lt ha)) (Nat.two_pow_pos w)
  by_cases he : a%A ≤ b%B
  all_goals
    simp [arithmetic, RegCode.exec, Function.update, h₁, h₂, h₃, h₄, h₅, h₆, h.zero, hword,
      Nat.sub_eq_zero_iff_le, he]
    constructor <;> first | exact h.srcBase | exact h.colBase | exact h.flag | exact h.zero | rfl


/-- Concatenate fixed-width little-endian exponent words in the given variable order. -/
def packed (w : ℕ) (xs : List ℕ) : List Bool := xs.flatMap (UniversalCountStack.digits w)

private def residuals (A B : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | n+1, a, b => residuals A B n (a/A) (b/B) ++ [b%B - a%A]

private def allows (A B : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n+1, a, b => decide (a%A ≤ b%B) && allows A B n (a/A) (b/B)

private theorem loop_run {w A B : ℕ} (hA : A < 2^w) (hB : B < 2^w) (n a b : ℕ)
    (ha : a < 2^w) (hb : b < 2^w) (reg : Regs 10 w) (good : Bool) (out : List Bool)
    (hr : Holds reg A B a b good) :
    ∃ k ≤ n*(bodyCost w+1)+1, ∃ R : Regs 10 w, machine.Runs k (frame reg n out)
      (frame R 0 (packed w (residuals A B n a b) ++ out)) ∧
      Holds R A B (a/A^n) (b/B^n) (good && allows A B n a b) := by
  induction n generalizing a b reg good out with
  | zero =>
    refine ⟨1, by simp, reg, ?_, by simpa [allows] using hr⟩
    simp only [residuals, packed, List.flatMap_nil, List.nil_append]
    exact Routine.Runs.popLoop_empty (Sum.inr Streams.marker : Port) (fun _ => true) (Routine.halt false) body.body (s := frame reg 0 out) rfl
  | succ n ih =>
    obtain ⟨s,hs,hbody⟩ := body_run reg n out
    obtain ⟨hr',hval⟩ := step_values hr hA hB ha hb
    rw [hval] at hbody
    obtain ⟨t,ht,R,htail,hreg⟩ := ih (a/A) (b/B) ((Nat.div_le_self ..).trans_lt ha) ((Nat.div_le_self ..).trans_lt hb)
      (arithmetic.exec reg) (good && decide (a%A ≤ b%B)) (wordBits (ISA.word w (b%B-a%A)) ++ out) hr'
    refine ⟨1+s+t, by rw [Nat.succ_mul]; omega, R, ?_, ?_⟩
    · have hsrc : frame reg (n+1) out (.inr .marker) = true :: List.replicate n true := by
        simp [frame, List.replicate_succ]
      have hruns := Routine.Runs.popLoop_true_continue (mid := frame (arithmetic.exec reg) n
        (wordBits (ISA.word w (b%B-a%A)) ++ out)) (.inr .marker) (fun _ => true) (Routine.halt false) body.body
        hsrc rfl (by rwa [frame_pop]) htail
      simpa only [machine, FiniteRoutine.repeatMarked, FiniteRoutine.Runs, FiniteRoutine.ofRoutine, UniversalCountStack.digits, ISA.word, residuals, packed, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using hruns
    · simpa only [Nat.div_div_eq_div_mul, pow_succ', allows, Bool.and_assoc] using hreg

private theorem residuals_eq (A B n a b : ℕ) :
    residuals A B n a b = List.ofFn (fun i : Fin n => b/B^i.rev.val%B - a/A^i.rev.val%A) := by
  induction n generalizing a b with
  | zero => simp [residuals]
  | succ n ih =>
    rw [residuals, ih, List.ofFn_succ']
    simp only [Fin.rev_castSucc, Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul,
      Fin.rev_last, Fin.val_zero, pow_zero, Nat.div_one, List.concat_eq_append]

private theorem allows_eq (A B n a b : ℕ) :
    allows A B n a b = true ↔ ∀ i : Fin n, a/A^i.rev.val%A ≤ b/B^i.rev.val%B := by
  induction n generalizing a b with
  | zero => simp [allows]
  | succ n ih =>
    rw [allows, Bool.and_eq_true, decide_eq_true_eq, ih, Fin.forall_fin_succ']
    simp only [Fin.rev_last, Fin.val_zero, pow_zero, Nat.div_one, Fin.rev_castSucc, Fin.val_succ,
      pow_succ', Nat.div_div_eq_div_mul]
    tauto

theorem raw_digit {t D : ℕ} (a : BoundedMonomial t D) (i : Fin t) :
    (rawCode a).val / (D+1)^i.rev.val % (D+1) = a.val i := by
  have h : t = i.rev.val + ((t-i.rev.val-1)+1) := by have := i.rev.isLt; omega
  have hpow : (D+1)^t = (D+1)^i.rev.val * ((D+1) * (D+1)^(t-i.rev.val-1)) := by
    conv_lhs => rw [h, pow_add, pow_succ']
  have hd := digit_rawCode a i
  change (rawCode a).val % (D+1)^t / (D+1)^i.rev.val % (D+1) = a.val i at hd
  rwa [hpow, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod] at hd

/-- Set the source and column radices and raw keys, initialize divisibility to true and clear
the scratch registers. -/
def initial (w L D row col : ℕ) : Regs 10 w :=
  ![ISA.word w (L+1), ISA.word w (D+1), ISA.word w row, ISA.word w col,
    ISA.word w 1, 0, 0, 0, 0, 0]

/-- A raw-key pair yields the actual ordered formal-polynomial exponent buffer
and the exact divisibility flag consumed by the equation-row dispatcher. -/
theorem pack_rows {w t L D : ℕ} (a : BoundedMonomial t L) (b : BoundedMonomial t D)
    (hL : rawSize t L ≤ 2^w) (hD : rawSize t D ≤ 2^w) (hLA : L+1 < 2^w) (hDB : D+1 < 2^w)
    (out : List Bool) :
    let reg := initial w L D (rawCode a).val (rawCode b).val
    let result := packed w (List.ofFn (fun i => b.val i - a.val i)) ++ out
    ∃ k ≤ t*(bodyCost w+1)+1, ∃ R : Regs 10 w, machine.Runs k (frame reg t out) (frame R 0 result) ∧
      R 4 = ISA.word w (decide (a.val ≤ b.val)).toNat := by
  intro reg result
  have hin : Holds reg (L+1) (D+1) (rawCode a).val (rawCode b).val true := by constructor <;> rfl
  obtain ⟨k,hk,R,run,hreg⟩ := loop_run hLA hDB t (rawCode a).val (rawCode b).val
    ((rawCode a).isLt.trans_le hL) ((rawCode b).isLt.trans_le hD) reg true out hin
  refine ⟨k,hk,R,?_,?_⟩
  · simpa only [residuals_eq, raw_digit, result] using run
  · have htest := allows_eq (L+1) (D+1) t (rawCode a).val (rawCode b).val
    simp only [raw_digit] at htest
    have he : allows (L+1) (D+1) t (rawCode a).val (rawCode b).val = decide (a.val ≤ b.val) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq, Finsupp.le_def] using htest
    simpa only [Bool.true_and, he] using hreg.flag

private theorem frame_length_le {w : ℕ} (R : Regs 10 w) (t : ℕ) (out : List Bool) (port : Port) :
    (frame R t out port).length ≤ max (max w t) out.length := by
  rcases port with j | j
  · exact (RegisterTable.bank_length_le Fin.elim0 0 R j).trans
      ((le_max_left w t).trans (le_max_left ..))
  · cases j <;> simp [frame]

theorem pack_rows_bounded {w t L D : ℕ} (a : BoundedMonomial t L) (b : BoundedMonomial t D)
    (hL : rawSize t L ≤ 2^w) (hD : rawSize t D ≤ 2^w) (hLA : L+1 < 2^w) (hDB : D+1 < 2^w)
    (out : List Bool) :
    let reg := initial w L D (rawCode a).val (rawCode b).val
    let result := packed w (List.ofFn (fun i => b.val i - a.val i)) ++ out
    let ticks := t*(bodyCost w+1)+1
    ∃ k ≤ ticks, ∃ R : Regs 10 w, machine.BoundedRun (max (max w t) out.length + ticks) k
      (frame reg t out) (frame R 0 result) ∧ R 4 = ISA.word w (decide (a.val ≤ b.val)).toNat := by
  obtain ⟨k,hk,R,hr,hgood⟩ := pack_rows a b hL hD hLA hDB out
  exact ⟨k,hk,R, UniversalCountStack.spaceRun_of_steps hr
    (fun j => Nat.add_le_add (frame_length_le _ _ _ j) hk),hgood⟩

end RadicalCertificate.MonomialIndex.ExponentPack

end VPVNP
end Computability
end OAI
