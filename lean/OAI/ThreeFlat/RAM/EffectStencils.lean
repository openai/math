import Mathlib.Data.ZMod.Defs
import OAI.ThreeFlat.RAM.DescriptorExpr
import OAI.ThreeFlat.RAM.EffectImage

namespace OAI
/-! # Pairing native address and value stencils for a chronological update stream -/

namespace ThreeFlat.RAM.ExpressionEffects

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Fin.CommRing

variable {w k : ℕ}

private def offset (base : Fin k) : Term w k 1 :=
  Term.binary .sub (.result 0) (.parameter base)

private def indexTerm (base : Fin k) : Term w k 1 :=
  Term.binary .div (offset base) (.literal 2)

/-- The two stencils take the update's ordinal as input. The compiled tape
expression selects its address or value according to the low bit of the offset. -/
def pairTerm (base : Fin k) (address value : Term w k 1) : Term w k 1 :=
  let side := Term.binary .mod (offset base) (.literal 2)
  let idx := indexTerm base
  Term.select .eq side (.literal 0) (address.instantiate (fun _ => idx))
    (value.instantiate (fun _ => idx))

theorem pairTerm_binds (base : Fin k) (address value : Term w k 1) :
    (pairTerm base address value).binds = address.binds+value.binds+14 := by
  simp [pairTerm, indexTerm, offset, Term.select, Term.binary, Term.binds, Term.literal,
    Term.parameter]; omega

theorem pairTerm_eval (base : Fin k) (address value : Term w k 1) (data : Fin k → Word w)
    (src : ℕ) (m : Memory w) (a : Word w) (hasBase : data base = (src : Word w))
    (le : src ≤ a.val) (two : 2 < 2^w) :
    let off := a.val-src
    let vs := fun _ : Fin 1 => ((off/2 : ℕ) : Word w)
    (pairTerm base address value).eval data m (fun _ => a) =
      if off%2 = 0 then address.eval data m vs else value.eval data m vs := by
  let off := a.val-src
  have fit : off < 2^w := lt_of_le_of_lt (Nat.sub_le ..) a.isLt
  have diff : a-(src : Word w) = (off : Word w) := by
    dsimp [off]
    rw [Nat.cast_sub le, Fin.cast_val_eq_self]
  have hoff : (offset base).eval data m (fun _ => a) = (off : Word w) := by
    simpa [offset, Term.eval, BinaryOp.eval, hasBase] using diff
  have hi : (indexTerm base).eval data m (fun _ => a) = ((off/2 : ℕ) : Word w) := by
    simp [indexTerm, hoff, BinaryOp.eval, Fin.val_cast_of_lt fit, Nat.mod_eq_of_lt two]
  have hs : (Term.binary .mod (offset base) (.literal 2)).eval data m (fun _ => a) =
      ((off%2 : ℕ) : Word w) := by
    simp [hoff, BinaryOp.eval, Fin.val_cast_of_lt fit, Nat.mod_eq_of_lt two]
  have eq : (((off%2 : ℕ) : Word w) = 0) ↔ off%2 = 0 := by
    rw [Fin.ext_iff, Fin.val_cast_of_lt (by omega : off%2 < 2^w)]
    rfl
  simp [pairTerm, hi, hs, Comparison.test, eq, off]

/-- Concrete chronological effects, computed by reading the source arrays. -/
def records (count : ℕ) (address value : Term w k 1) (params : Fin k → Word w) (m : Memory w) :
    List (EffectStream.Record w) :=
  List.ofFn fun i : Fin count =>
    (address.eval params m (fun _ => (i.val : Word w)), value.eval params m (fun _ => (i.val : Word w)))

@[simp] theorem records_length (count : ℕ) (address value : Term w k 1) (p : Fin k → Word w)
    (m : Memory w) : (records count address value p m).length = count := by simp [records]

theorem pairTerm_packed (base : Fin k) (address value : Term w k 1) (params : Fin k → Word w)
    (count src : ℕ) (input scratch : Memory w) (a : Word w)
    (hasBase : params base = (src : Word w)) (lo : src ≤ a.val) (hi : a.val < src+2*count)
    (fits : src+2*count < 2^w)
    (frame : ∀ i : Fin count, ∀ e ∈ [address,value],
      e.eval params scratch (fun _ => (i.val : Word w)) =
        e.eval params input (fun _ => (i.val : Word w))) :
    (pairTerm base address value).eval params scratch (fun _ => a) =
      EffectStream.packedWord src (records count address value params input) a.val := by
  have two : 2 < 2^w := by omega
  let i : Fin count := ⟨(a.val-src)/2, by omega⟩
  let updates := records count address value params input
  let j : Fin updates.length := ⟨i.val, by simp [updates]⟩
  have sameA := frame i address (by simp)
  have sameV := frame i value (by simp)
  rw [pairTerm_eval base address value params src scratch a hasBase lo two]
  by_cases even : (a.val-src)%2 = 0
  · rw [ite_eq_left even]
    have pos : a.val = src+2*j.val := by dsimp [j, i]; omega
    conv_rhs => rw [pos, EffectStream.packedWord_address]
    simpa [j, updates, records] using sameA
  · rw [ite_eq_right even]
    have pos : a.val = src+2*j.val+1 := by dsimp [j, i]; omega
    conv_rhs => rw [pos, EffectStream.packedWord_value]
    simpa [j, updates, records] using sameV

end ThreeFlat.RAM.ExpressionEffects

end OAI
