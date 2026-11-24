import OAI.Computability.VPVNP.EvaluatorIndexChoice
import OAI.Computability.VPVNP.EvaluatorSafetyTransfer
import OAI.Computability.VPVNP.SliceArithmeticWord

/-!
# Reading the unit coordinate and branching on the final residue

The basis list of Lemma 8.2 starts at the unit, with ordinal zero. A path
ending elsewhere rejects. At ordinal zero the machine reads only the first
limb of the accumulated field product. The width stack supplies the number
of bits to read, so higher polynomial-basis coefficients never enter the
residue comparison.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.Output

open RAMTape

/-- The basis ordinal, limb-width tally and accumulated field product read by the terminal
residue test. -/
inductive Port where
  | index | width | product
  deriving DecidableEq

instance : Fintype Port := ⟨{.index, .width, .product}, fun j ↦ by cases j <;> simp⟩

/-- Control for testing the unit ordinal and comparing successive guessed bits with the low
limb of the accumulated product. -/
inductive Phase where
  | endpoint
  | width (less : Bool)
  | limb (less : Bool)
  | choose (less bit : Bool)
  | halt (accept : Bool)
  deriving DecidableEq, Fintype

private def compareBit (less x y : Bool) : Bool := if x = y then less else y

/-- The bound comparison runs from low to high bits. On exhaustion the two
possible branch targets already encode the comparison of the whole word. -/
def routine : Routine Port Phase where
  entry := .endpoint
  code
    | .endpoint => .pop .index fun b ↦ some (match b with
      | none => .width false | some false => .endpoint | some true => .halt false)
    | .width less => .pop .width fun b ↦ some (if b.isSome then .limb less else .halt less)
    | .limb less => .pop .product fun b ↦ some (b.elim (.halt false) (.choose less))
    | .choose less b => .choose (some (.width (compareBit less false b)))
        (some (.width (compareBit less true b)))
    | .halt accept => .halt accept

/-- The named stacks used by the terminal reader. All other stacks of the
whole evaluator can be framed around this routine. -/
def bank (idx width product : List Bool) : Stacks Port
  | .index => idx | .width => width | .product => product

private theorem update_idx (idx ws prod idx' : List Bool) :
    Function.update (bank idx ws prod) .index idx' = bank idx' ws prod := by funext k; cases k <;> rfl

private theorem update_width (idx ws prod ws' : List Bool) :
    Function.update (bank idx ws prod) .width ws' = bank idx ws' prod := by funext k; cases k <;> rfl

private theorem update_prod (idx ws prod prod' : List Bool) :
    Function.update (bank idx ws prod) .product prod' = bank idx ws prod' := by funext k; cases k <;> rfl

private theorem count_width (bits tail idx : List Bool) (fuel : ℕ) (less : Bool)
    (c : ℕ → Stacks Port → ℕ) :
    routine.countFrom c (fuel+(3*bits.length+2)) (some (.width less))
        (bank idx (List.replicate bits.length true) (bits ++ tail)) =
      TapeWord.value bits + less.toNat := by
  induction bits generalizing less with
  | nil => simp [Routine.countFrom, routine, bank, TapeWord.value]
  | cons b bits ih =>
    have step (r : ℕ) :
        routine.countFrom c (r+3) (some (.width less))
            (bank idx (true::List.replicate bits.length true) (b::bits ++ tail)) =
          routine.countFrom c r (some (.width (compareBit less false b)))
            (bank idx (List.replicate bits.length true) (bits ++ tail)) +
          routine.countFrom c r (some (.width (compareBit less true b)))
            (bank idx (List.replicate bits.length true) (bits ++ tail)) := by
      simp only [Routine.countFrom, routine, bank, List.head?_cons, List.tail_cons, List.cons_append,
        Option.isSome_some, ite_true, update_width, Option.elim_some, update_prod]
    rw [show fuel+(3*(b::bits).length+2) = (fuel+(3*bits.length+2))+3 by simp; omega,
      List.length_cons, List.replicate_succ, step, ih, ih]
    cases less <;> cases b <;> simp [compareBit, TapeWord.value] <;> omega

/-- With a correct endpoint the continuation is never entered: every accepted
guess halts directly. The result is the ordinary natural value of the low limb. -/
theorem count_output (idx bits tail : List Bool) (fuel : ℕ) (c : ℕ → Stacks Port → ℕ) :
    routine.count c (fuel + (3*bits.length+3) + idx.length)
        (bank idx (List.replicate bits.length true) (bits ++ tail)) =
      if TapeWord.value idx = 0 then TapeWord.value bits else 0 := by
  induction idx with
  | nil =>
    rw [show fuel + (3*bits.length+3) + [].length = (fuel+(3*bits.length+2))+1 by simp; omega]
    change routine.countFrom c _ (some .endpoint) _ = _
    rw [Routine.countFrom]
    simp only [routine, bank, List.head?_nil, List.tail_nil, update_idx, TapeWord.value, ite_true]
    exact (count_width bits tail [] fuel false c).trans (by simp)
  | cons b idx ih =>
    rw [List.length_cons, Nat.add_succ]
    change routine.countFrom c _ (some .endpoint) _ = _
    rw [Routine.countFrom]
    cases b with
    | false => simpa only [routine, bank, List.head?_cons, List.tail_cons, update_idx, TapeWord.value,
        Bool.toNat_false, zero_add, Nat.mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using ih
    | true =>
      rw [show fuel + (3*bits.length+3) + idx.length = (fuel + (3*bits.length+2) + idx.length)+1 by omega]
      simp [routine, bank, Routine.countFrom, TapeWord.value]

/-- Applied to the field representation, the terminal machine counts the
low prime-field coefficient if and only if the final ordinal is zero. -/
theorem count_output_limb {p w v : ℕ} [NeZero p] (hw : SliceArithmetic.Word.workingWidth p ≤ w)
    (i : BurstRAM.Word v) (r : Fin p) (tail : List Bool) (fuel : ℕ) (c : ℕ → Stacks Port → ℕ) :
    routine.count c (fuel + (3*w+3) + v)
      (bank (BurstRAM.wordBits i) (List.replicate w true)
        (BurstRAM.wordBits (SliceArithmetic.Word.limb w r) ++ tail)) =
      if i.val = 0 then r.val else 0 := by
  simpa only [BurstRAM.length_wordBits, TapeWord.value_wordBits, SliceArithmetic.Word.limb_val hw] using
    count_output (BurstRAM.wordBits i) (BurstRAM.wordBits (SliceArithmetic.Word.limb w r)) tail fuel c

private theorem allStops_width (ws prod idx : List Bool) (less : Bool) (cont : ℕ → Stacks Port → Prop) :
    routine.AllStopsFrom cont (3*ws.length+2) (some (.width less)) (bank idx ws prod) := by
  induction ws generalizing less prod with
  | nil => simp [Routine.AllStopsFrom, routine, bank]
  | cons w ws ih =>
    rw [show 3*(w::ws).length+2 = (3*ws.length+2)+3 by simp; omega]
    cases prod with
    | nil =>
      have reject (n : ℕ) : routine.AllStopsFrom cont (n+3) (some (.width less)) (bank idx (w::ws) []) := by
        simp [Routine.AllStopsFrom, routine, bank]
      exact reject _
    | cons b prod =>
      have step (n : ℕ) : routine.AllStopsFrom cont (n+3) (some (.width less)) (bank idx (w::ws) (b::prod)) ↔
          routine.AllStopsFrom cont n (some (.width (compareBit less false b))) (bank idx ws prod) ∧
          routine.AllStopsFrom cont n (some (.width (compareBit less true b))) (bank idx ws prod) := by
        simp only [Routine.AllStopsFrom, routine, bank, List.head?_cons, List.tail_cons,
          Option.isSome_some, ite_true, update_width, Option.elim_some, update_prod]
      exact (step _).mpr ⟨ih _ _, ih _ _⟩

/-- Every terminal branch halts within its linear clock. The endpoint and low
limb tests only consume their inputs, including on a rejecting branch. -/
theorem allStops_output (idx ws prod : List Bool) (cont : ℕ → Stacks Port → Prop) :
    routine.AllStops cont (3*ws.length+3+idx.length) (bank idx ws prod) := by
  induction idx with
  | nil =>
    rw [show 3*ws.length+3+[].length = (3*ws.length+2)+1 by simp]
    change routine.AllStopsFrom cont _ (some .endpoint) _
    rw [Routine.AllStopsFrom]
    simp only [routine, bank, List.head?_nil, List.tail_nil, update_idx]
    exact allStops_width ws prod [] false cont
  | cons b idx ih =>
    rw [List.length_cons, Nat.add_succ]
    change routine.AllStopsFrom cont _ (some .endpoint) _
    rw [Routine.AllStopsFrom]
    cases b with
    | false => simpa only [routine, bank, List.head?_cons, List.tail_cons, update_idx] using ih
    | true =>
      rw [show 3*ws.length+3+idx.length = (3*ws.length+2+idx.length)+1 by omega]
      simp [Routine.AllStopsFrom, routine, bank]

end Evaluator.Output

end VPVNP
end Computability
end OAI
