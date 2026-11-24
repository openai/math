import OAI.Computability.VPVNP.RAMWordBits
import Mathlib.Data.Nat.Bitwise

/-!
# Little-endian bit scans for the word RAM

A word occupies one stack cell per bit. The elementary binary transducers
scan two equal-length stacks from low to high, remembering one carry or
borrow bit in their finite control. The final carry or borrow certifies the
arithmetic even when the result wraps around.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord

/-- Unsigned value of a little-endian list of bits, with the empty list representing zero. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: xs => b.toNat + 2 * value xs

theorem value_lt (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b <;> simp only [value, Bool.toNat_true, Bool.toNat_false, List.length_cons, pow_succ] <;> omega

theorem value_ofFn (w : ℕ) (d : Fin w → Bool) :
    value (List.ofFn d) = ∑ i, (d i).toNat * 2 ^ i.val := by
  induction w with
  | zero => simp [value]
  | succ w ih =>
    rw [List.ofFn_succ, value, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← Nat.mul_assoc,
      ← Finset.sum_mul]
    rw [Nat.mul_comm]

theorem value_wordBits {w : ℕ} (a : BurstRAM.Word w) : value (BurstRAM.wordBits a) = a.val := by
  let d := RAMSerialization.wordBits w a
  have he : ((RAMSerialization.wordBits w).symm d).val =
      ∑ i, (finTwoEquiv.symm (d i)).val * 2 ^ i.val := finFunctionFinEquiv_apply _
  have hd (i : Fin w) : (finTwoEquiv.symm (d i)).val = (d i).toNat := by cases d i <;> rfl
  rw [show (RAMSerialization.wordBits w).symm d = a from Equiv.symm_apply_apply _ _] at he
  simpa only [BurstRAM.wordBits, value_ofFn, hd] using he.symm

theorem eq_of_length_value {xs ys : List Bool} (hlen : xs.length = ys.length)
    (hval : value xs = value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons d ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      cases b <;> cases d <;> simp only [value, Bool.toNat_true, Bool.toNat_false] at hval <;>
        first | exact congrArg (_ :: ·) (ih hlen (by omega)) | omega

/-- A synchronous transducer. When the inputs are equally long it reads one
bit from each stack per emitted bit and leaves its final control state. -/
def scan (step : Bool → Bool → Bool → Bool × Bool) : Bool → List Bool → List Bool → List Bool × Bool
  | c, b :: bs, d :: ds =>
    let (out, next) := step c b d
    let (rest, final) := scan step next bs ds
    (out :: rest, final)
  | c, _, _ => ([], c)

theorem length_scan (step : Bool → Bool → Bool → Bool × Bool) (c : Bool) (x y : List Bool)
    (hlen : x.length = y.length) : (scan step c x y).1.length = x.length := by
  induction x generalizing c y with
  | nil => rfl
  | cons b bs ih =>
    cases y with
    | nil => simp at hlen
    | cons d ds => simp [scan, ih _ _ (Nat.succ.inj hlen)]

/-- Compute the sum bit and outgoing carry for two operand bits and an incoming carry. -/
def addBit (c b d : Bool) : Bool × Bool :=
  ((b ^^ d) ^^ c, (b && d) || (c && (b ^^ d)))

/-- Compute the difference bit and outgoing borrow for two operand bits and an incoming borrow. -/
def subBit (c b d : Bool) : Bool × Bool :=
  ((b ^^ d) ^^ c, (!b && d) || (c && !(b ^^ d)))

/-- Scan paired little-endian bits with a carry and return the sum bits and final carry when
either input ends. -/
abbrev addScan := scan addBit
/-- Scan paired little-endian bits with a borrow and return the difference bits and final
borrow when either input ends. -/
abbrev subScan := scan subBit

theorem length_addScan {c : Bool} {x y : List Bool} (hlen : x.length = y.length) :
    (addScan c x y).1.length = x.length := length_scan _ _ _ _ hlen

theorem length_subScan {c : Bool} {x y : List Bool} (hlen : x.length = y.length) :
    (subScan c x y).1.length = x.length := length_scan _ _ _ _ hlen

theorem addScan_spec {c : Bool} {x y : List Bool} (hlen : x.length = y.length) :
    value (addScan c x y).1 + 2 ^ x.length * (addScan c x y).2.toNat =
      value x + value y + c.toNat := by
  induction x generalizing c y with
  | nil => cases y <;> simp_all [addScan, scan, value]
  | cons b bs ih =>
    cases y with
    | nil => simp at hlen
    | cons d ds =>
      have h := ih (c := (addBit c b d).2) (Nat.succ.inj hlen)
      have hlow : (addBit c b d).1.toNat + 2 * (addBit c b d).2.toNat =
          b.toNat + d.toNat + c.toNat := by cases c <;> cases b <;> cases d <;> decide
      simp only [addScan] at h
      simp only [addScan, scan, value, List.length_cons, pow_succ, Nat.mul_right_comm _ 2 _]
      omega

theorem subScan_spec {c : Bool} {x y : List Bool} (hlen : x.length = y.length) :
    value (subScan c x y).1 + value y + c.toNat =
      value x + 2 ^ x.length * (subScan c x y).2.toNat := by
  induction x generalizing c y with
  | nil => cases y <;> simp_all [subScan, scan, value]
  | cons b bs ih =>
    cases y with
    | nil => simp at hlen
    | cons d ds =>
      have h := ih (c := (subBit c b d).2) (Nat.succ.inj hlen)
      have hlow : (subBit c b d).1.toNat + d.toNat + c.toNat =
          b.toNat + 2 * (subBit c b d).2.toNat := by cases c <;> cases b <;> cases d <;> decide
      simp only [subScan] at h
      simp only [subScan, scan, value, List.length_cons, pow_succ, Nat.mul_right_comm _ 2 _]
      omega

/-- Parallel Boolean operations use the same scan with a single dummy state. -/
abbrev logicScan (op : Bool → Bool → Bool) := scan (fun _ b d => (op b d, false)) false

theorem logicScan_spec {op : Bool → Bool → Bool} (hzero : op false false = false)
    {x y : List Bool} (hlen : x.length = y.length) :
    value (logicScan op x y).1 = Nat.bitwise op (value x) (value y) := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [value, logicScan, scan]
  | cons b bs ih =>
    cases y with
    | nil => simp at hlen
    | cons d ds =>
      have hbit (e : Bool) (n : ℕ) : Nat.bit e n = e.toNat + 2 * n := by
        cases e <;> simp [Nat.bit, Nat.add_comm]
      simp only [logicScan, scan, value]
      rw [← hbit b, ← hbit d, Nat.bitwise_bit hzero, hbit, ← ih (Nat.succ.inj hlen)]

end TapeWord

end VPVNP
end Computability
end OAI
