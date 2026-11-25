import OAI.Computability.BorderVNP.RoutingISATableSetup
import OAI.Computability.VPVNP.RAMTapeWord
import Mathlib.Data.Nat.Size

/-! # Installing a fixed finite table through ordinary word instructions

Fixed gadget tables may be larger than the instruction set's immediate
literals. Each entry is constructed one binary digit at a time and stored
at its consecutive allocated address. The code depends only on the fixed
finite table. Its instruction count is independent of the processor input,
team count and runtime word width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Constants

open VPVNP VPVNP.BurstRAM

/-- Digits for a natural number, using its own minimal binary width. -/
def digits (x : ℕ) : List Bool := BurstRAM.wordBits (⟨x,Nat.lt_size_self x⟩ : Word x.size)

/-- Build one fixed value in register 58; register 57 holds one. -/
def literal : List Bool → Code
  | [] => .constant 58 0
  | b::bs => .seq (literal bs) (.seq (.binary .add 58 58 58)
      (if b then .binary .add 58 58 57 else .nop))

/-- Emit the indicated word, then advance the memory cursor. -/
def emitWord (x : ℕ) : Code :=
  .seq (literal (digits x)) (.seq (.store 56 58) (.binary .add 56 56 57))

/-- Statically linked word construction and consecutive stores. -/
def emitWords : List ℕ → Code
  | [] => .nop
  | x::xs => .seq (emitWord x) (emitWords xs)

/-- Set the output cursor from the real frame and install the table. -/
def atField (field : Word 8) (xs : List ℕ) : Code :=
  .block [readFrame 56 62 63 field,.constant 57 1,emitWords xs]

/-- The digits used to synthesize an entry decode to the prescribed natural. -/
theorem digits_value (x : ℕ) : TapeWord.value (digits x) = x := TapeWord.value_wordBits _

private theorem literal_eval (bits : List Bool) (pub : Arg → ℕ) (z : NatState) (one : z.reg 57 = 1) :
    (literal bits).fixedEval pub z =
      ⟨Function.update z.reg 58 (TapeWord.value bits),z.mem⟩ := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp (config := {decide:=true}) [literal, Code.fixedEval, Code.evalNat,
      ih, addressOp, TapeWord.value, one, Nat.two_mul, Nat.add_comm]

private theorem literal_safe (bits : List Bool) (w : ℕ) (pub : Arg → ℕ) (z : NatState)
    (one : z.reg 57=1) (room : TapeWord.value bits < 2^w) :
    (literal bits).fixedSafe w pub z := by
  induction bits with
  | nil => exact Nat.two_pow_pos w
  | cons b bs ih =>
    have tail : TapeWord.value bs < 2^w := by cases b <;> simp [TapeWord.value] at room <;> omega
    have head := ih tail
    cases b <;> simp (config := {decide:=true}) [literal,Code.fixedSafe,Code.fixedEval,Code.evalNat,
      Code.safeReadOnly,addressOpFits,addressOp,literal_eval bs pub z one,one,head] <;>
      simp [TapeWord.value] at room <;> omega

/-- Synthesizing a representable natural with register 57 set to one safely writes
that natural to register 58 and preserves the rest of the state. -/
theorem literal_word_effect (x w : ℕ) (pub : Arg → ℕ) (z : NatState)
    (one : z.reg 57 = 1) (room : x < 2^w) :
    (literal (digits x)).fixedSafe w pub z ∧
      (literal (digits x)).fixedEval pub z = ⟨Function.update z.reg 58 x, z.mem⟩ := by
  rw [← digits_value x] at room
  refine ⟨literal_safe _ w pub z one room, ?_⟩
  simpa only [digits_value] using literal_eval (digits x) pub z one

/-- The full resulting memory after storing all the prescribed values. -/
def image : ℕ → List ℕ → (ℕ → ℕ) → ℕ → ℕ
  | _, [], m => m
  | p, a::as, m => image (p+1) as (Function.update m p a)

/-- The installed natural at every index is the prescribed finite-table word. -/
theorem image_at (p : ℕ) (xs : List ℕ) (m : ℕ → ℕ) (i : Fin xs.length) :
    image p xs m (p+i.val) = xs[i.val] := by
  have off (ys : List ℕ) (q a : ℕ) (h : a < q) (m' : ℕ → ℕ) : image q ys m' a = m' a := by
    induction ys generalizing q m' with
    | nil => rfl
    | cons y ys ih => rw [image,ih _ (by omega) _,Function.update_of_ne (by omega)]
  induction xs generalizing p m with
  | nil => exact Fin.elim0 i
  | cons a as ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [image,off as (p+1) p (by omega)]
    · simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (p+1) (Function.update m p a) j

/-- Outside the actual table, installing it preserves the old word. -/
theorem image_outside (p : ℕ) (xs : List ℕ) (m : ℕ → ℕ) (a : ℕ)
    (h : a < p ∨ p+xs.length ≤ a) : image p xs m a = m a := by
  induction xs generalizing p m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at h
    rw [image, ih _ _ (by omega), Function.update_of_ne (by omega)]

private theorem emitWords_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (xs : List ℕ) (p : ℕ) (s : Bank w) (m : Memory w)
    (cursor : readings s 56 = p) (one : readings s 57 = 1)
    (room : p+xs.length < 2^w) (values : ∀ x ∈ xs, x < 2^w) :
    BoundedRun pub mac (emitWords xs) s m (emitWords xs).slots
      (fun z ↦ z.mem = image p xs (readings m)) := by
  induction xs generalizing p s m with
  | nil => exact ⟨_,s,m,Runs.localStep m rfl rfl,le_rfl,rfl⟩
  | cons x xs ih =>
    have vx := values x (by simp)
    have succ : p+1 < 2^w := by simp at room; omega
    let z := NatState.ofWords s m
    have r56 : z.reg 56 = p := cursor
    have r57 : z.reg 57 = 1 := one
    have orig : z.mem = readings m := rfl
    have lit := literal_safe (digits x) w (readings pub) z one (by rwa [digits_value])
    have val := literal_eval (digits x) (readings pub) z one
    have safe : (emitWord x).fixedSafe w (readings pub) z := by
      simp (config := {decide:=true}) [emitWord,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
        addressOpFits,lit,val,r57,r56,succ]
    apply ((emitWord x).runFixed pub mac s m safe).seq
    intro t mt h
    change NatState.ofWords t mt = (emitWord x).fixedEval (readings pub) z at h
    have result : readings t 56 = p+1 ∧ readings t 57 = 1 ∧ readings mt = Function.update (readings m) p x := by
      change (NatState.ofWords t mt).reg 56 = _ ∧ (NatState.ofWords t mt).reg 57 = _ ∧
        (NatState.ofWords t mt).mem = _
      rw [h]
      simp (config := {decide:=true}) [emitWord, Code.fixedEval, Code.evalNat,val,r56,r57,orig,addressOp,digits_value]
    obtain ⟨next,kept,updated⟩ := result
    have tail := ih (p+1) t mt next kept (by simp at room; omega) (fun y hy ↦ values y (by simp [hy]))
    exact tail.mono le_rfl (fun st hs ↦ by simpa only [image,←updated] using hs)

/-- On a real addressed destination and representable table entries, the
emitted finite program constructs the exact table within its fixed slot count. -/
theorem atField_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (field : Word 8) (xs : List ℕ) (p : ℕ)
    (hf : readings pub 0+field.val < 2^w) (hp : readings m (readings pub 0+field.val) = p)
    (hw : 1 < 2^w) (room : p+xs.length < 2^w) (values : ∀ x ∈ xs, x < 2^w) :
    BoundedRun pub mac (atField field xs) s m (atField field xs).slots
      (fun z ↦ z.mem = image p xs (readings m)) := by
  apply ((readFrame 56 62 63 field).runFixed pub mac s m (readFrame_fixedSafe _ _ _ _ _ hf)).seq
  intro t mt h
  have cur : readings t 56=p ∧ readings mt = readings m := by
    change (NatState.ofWords t mt).reg 56=p ∧ (NatState.ofWords t mt).mem=_
    rw [h,readFrame_fixedEval]
    simp [NatState.ofWords,hp]
  let u := Function.update t 57 (Fin.ofNat (2^w) 1)
  have init : Runs pub mac (.constant 57 1) t mt [tick w] u mt := Runs.localStep mt rfl rfl
  have one : readings u 57=1 := by simp [readings,u,Nat.mod_eq_of_lt hw]
  have start : readings u 56=p := by simpa (config := {decide:=true}) [readings,u] using cur.1
  obtain ⟨fs,v,mv,tail,cost,out⟩ := emitWords_run pub mac xs p u mt start one room values
  refine ⟨_,v,mv,init.seq tail,?_,by simpa only [cur.2] using out⟩
  change 1 + traceCost fs ≤ 1 + (emitWords xs).slots
  omega

end RoutingISA.Constants

end BorderVNP
end Computability
end OAI
