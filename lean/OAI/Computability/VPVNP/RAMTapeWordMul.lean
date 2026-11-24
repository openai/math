import OAI.Computability.VPVNP.RAMProgram
import OAI.Computability.VPVNP.RAMTapeStacks
import OAI.Computability.VPVNP.RAMTapeWordMulValue
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

/-!
# Fixed bit-stack control for word multiplication

The multiplier is read from least to most significant bit. Each round
simultaneously shifts the multiplicand and conditionally adds it into the
accumulator, discarding overflow at the width of the input stacks. Two
scratch stacks restore both words to least-significant-bit-first order.
The number of control states and stacks is independent of the word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Mul

open RAMTape

/-- Bit stacks for the multiplier, multiplicand, running accumulator and temporary shifted and
summed words. -/
inductive Reg
  | multiplier | multiplicand | accumulator | shifted | sum
  deriving DecidableEq

instance : Fintype Reg :=
  ⟨{.multiplier, .multiplicand, .accumulator, .shifted, .sum},
    fun k => by cases k <;> simp⟩

/-- Control states for initialization and for the shift-and-add rounds that consume successive
multiplier bits. -/
inductive State
  | init | saveInit (bit : Bool) | zeroInit | restoreInit | pushInit (bit : Bool)
  | loop | scanX (use carry previous : Bool) | scanAcc (use carry previous x : Bool)
  | saveX (use next previous x out : Bool) | saveSum (use next x out : Bool)
  | reverseX | reverseSum (x : Bool) | putX (x a : Bool) | putSum (a : Bool)
  | discard | done | fail
  deriving DecidableEq, Fintype

/-- The only data in finite control are the handful of bits between pop and
push instructions. Inputs are copied into these stacks by the caller. -/
def code : StackCode Reg State
  | .init => .pop .multiplicand fun b => b.elim .restoreInit .saveInit
  | .saveInit b => .push .shifted b .zeroInit
  | .zeroInit => .push .accumulator false .init
  | .restoreInit => .pop .shifted fun b => b.elim .loop .pushInit
  | .pushInit b => .push .multiplicand b .restoreInit
  | .loop => .pop .multiplier fun b => b.elim .discard (fun use => .scanX use false false)
  | .scanX use carry previous =>
    .pop .multiplicand fun b => b.elim .reverseX (.scanAcc use carry previous)
  | .scanAcc use carry previous b => .pop .accumulator fun d =>
    d.elim .fail fun bit =>
      let step := addBit carry (use && b) bit
      .saveX use step.2 previous b step.1
  | .saveX use next previous b out => .push .shifted previous (.saveSum use next b out)
  | .saveSum use next b out => .push .sum out (.scanX use next b)
  | .reverseX => .pop .shifted fun b => b.elim .loop .reverseSum
  | .reverseSum b => .pop .sum fun a => a.elim .fail (.putX b)
  | .putX b a => .push .multiplicand b (.putSum a)
  | .putSum a => .push .accumulator a .reverseX
  | .discard => .pop .multiplicand fun b => b.elim .done (fun _ => .discard)
  | .done => .halt true
  | .fail => .halt false

/-- Install the five bit lists as the current multiplication operands, accumulator and
temporary words. -/
def store (bits x acc xr ar : List Bool) : Stacks Reg
  | .multiplier => bits
  | .multiplicand => x
  | .accumulator => acc
  | .shifted => xr
  | .sum => ar

private theorem update_store (bits x acc xr ar word : List Bool) (k : Reg) :
    Function.update (store bits x acc xr ar) k word = match k with
      | .multiplier => store word x acc xr ar
      | .multiplicand => store bits word acc xr ar
      | .accumulator => store bits x word xr ar
      | .shifted => store bits x acc word ar
      | .sum => store bits x acc xr word := by
  funext i
  cases k <;> cases i <;> simp [store]

-- The instruction choice must reduce to a literal push or pop.
local macro "mul_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_store])

private theorem scan_run (use carry prev : Bool) (bits x acc xr ar : List Bool)
    (hlen : acc.length = x.length) :
    StackRuns code (4 * x.length + 1) (.scanX use carry prev) (store bits x acc xr ar)
      .reverseX (store bits [] [] ((mulScan use carry prev x acc).1.reverse ++ xr)
        ((mulScan use carry prev x acc).2.reverse ++ ar)) := by
  induction x generalizing carry prev acc xr ar with
  | nil =>
    have he : acc = [] := List.length_eq_zero_iff.mp hlen
    subst acc
    mul_step
    exact .nil ..
  | cons b x ih =>
    cases acc with
    | nil => simp at hlen
    | cons d acc =>
      have ht := ih (addBit carry (use && b) d).2 b acc (prev :: xr)
        ((addBit carry (use && b) d).1 :: ar) (Nat.succ.inj hlen)
      simp only [List.length_cons, Nat.mul_succ, mulScan, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      mul_step
      mul_step
      mul_step
      mul_step
      exact ht

private theorem reverse_run (bits x acc xr ar : List Bool) (hlen : ar.length = xr.length) :
    StackRuns code (4 * xr.length + 1) .reverseX (store bits x acc xr ar)
      .loop (store bits (xr.reverse ++ x) (ar.reverse ++ acc) [] []) := by
  induction xr generalizing x acc ar with
  | nil =>
    have he : ar = [] := List.length_eq_zero_iff.mp hlen
    subst ar
    mul_step
    exact .nil ..
  | cons b xr ih =>
    cases ar with
    | nil => simp at hlen
    | cons d ar =>
      simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      mul_step
      mul_step
      mul_step
      mul_step
      exact ih (b :: x) (d :: acc) ar (Nat.succ.inj hlen)

private theorem discard_run (x acc : List Bool) :
    StackRuns code (x.length + 1) .discard (store [] x acc [] []) .done (store [] [] acc [] []) := by
  induction x with
  | nil => mul_step; exact .nil ..
  | cons b x ih => simp only [List.length_cons]; mul_step; exact ih

/-- Consume the multiplier and compute a multiply-add, with wraparound. -/
theorem loop_run (bits x acc : List Bool) (hlen : acc.length = x.length) :
    StackRuns code (bits.length * (8 * x.length + 3) + (x.length + 2))
      .loop (store bits x acc [] []) .done (store [] [] (mulFold bits x acc) [] []) := by
  induction bits generalizing x acc with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, mulFold]
    mul_step
    exact discard_run x acc
  | cons use bits ih =>
    let p := mulRound use x acc
    obtain ⟨hx, ha⟩ := length_mulRound use hlen
    have scan := scan_run use false false bits x acc [] [] hlen
    have rev := reverse_run bits [] [] p.1.reverse p.2.reverse (by simp [p, hx, ha])
    have h1 : StackRuns code (4 * x.length + 1) (.scanX use false false)
        (store bits x acc [] []) .reverseX (store bits [] [] p.1.reverse p.2.reverse) := by
      simpa [p, mulRound] using scan
    have h2 : StackRuns code (4 * x.length + 1) .reverseX
        (store bits [] [] p.1.reverse p.2.reverse) .loop (store bits p.1 p.2 [] []) := by
      simpa [p, hx] using rev
    have h3 := ih p.1 p.2 (ha.trans hx.symm)
    rw [show p.1.length = x.length from hx] at h3
    have htotal : (use :: bits).length * (8 * x.length + 3) + (x.length + 2) =
        ((4 * x.length + 1) + (4 * x.length + 1) +
        (bits.length * (8 * x.length + 3) + (x.length + 2))) + 1 := by
      simp only [List.length_cons]
      ring
    rw [htotal]
    mul_step
    exact (h1.trans h2).trans h3

private theorem init_run (bits x acc xr : List Bool) :
    StackRuns code (3 * x.length + 1) .init (store bits x acc xr [])
      .restoreInit (store bits [] (List.replicate x.length false ++ acc) (x.reverse ++ xr) []) := by
  induction x generalizing acc xr with
  | nil => mul_step; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.replicate_succ']
    mul_step
    mul_step
    mul_step
    exact ih (false :: acc) (b :: xr)

private theorem init_restore (bits x acc xr : List Bool) :
    StackRuns code (2 * xr.length + 1) .restoreInit (store bits x acc xr [])
      .loop (store bits (xr.reverse ++ x) acc [] []) := by
  induction xr generalizing x with
  | nil => mul_step; exact .nil ..
  | cons b xr ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    mul_step
    mul_step
    exact ih (b :: x)

/-- Start with two words and empty work stacks. The accumulator is initialized
to a zero word of the multiplicand's width. All four other stacks are empty at
exit. For equal widths `w` the time is `8*w² + 9*w + 4`. -/
theorem multiply_run (bits x : List Bool) :
    StackRuns code (bits.length * (8 * x.length + 3) + (6 * x.length + 4))
      .init (store bits x [] [] []) .done
      (store [] [] (mulFold bits x (List.replicate x.length false)) [] []) := by
  let acc := List.replicate x.length false
  have h1 := init_run bits x [] []
  have h2 := init_restore bits [] acc x.reverse
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2
  have h3 := loop_run bits x acc (by simp [acc])
  convert (h1.trans h2).trans h3 using 1
  ring

/-- The multiplication opcode, at every word width, is implemented by this
single finite control. Each input and output uses the RAM word bit encoding. -/
theorem multiply_word_run {w : ℕ} (a b : BurstRAM.Word w) :
    StackRuns code (8 * w ^ 2 + 9 * w + 4) .init
      (store (BurstRAM.wordBits b) (BurstRAM.wordBits a) [] [] []) .done
      (store [] [] (BurstRAM.wordBits (BurstRAM.PrivateRAM.BinaryOp.mul.eval a b)) [] []) := by
  have h := multiply_run (BurstRAM.wordBits b) (BurstRAM.wordBits a)
  simp only [BurstRAM.length_wordBits, mulFold_wordBits] at h
  rw [show 8 * w ^ 2 + 9 * w + 4 = w * (8 * w + 3) + (6 * w + 4) by ring]
  exact h

end TapeWord.Mul

end VPVNP
end Computability
end OAI
