import OAI.Computability.BorderVNP.DiagonalTallyGather

/-! # Native materialization of assignment-dependent tally records

The public description of a record contains a coordinate base, an address of a
coordinate offset, a half-open vector of bit addresses, and an address of a shift.
The offset and shift words can be delivered fields of the selected batch. Digits come
from the verified cell report or from a packet's actual assignment. Only the output
pair contains the resulting coordinate and the shifted value.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyMaterialize

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM DiagonalTallyGather

/-- One physical operand with the mathematical values witnessed by the delivered
words and the assignments at its named bit addresses. -/
structure Operand where
  /-- Fixed part of the coordinate, such as the number of parameter coordinates. -/
  base : ℕ
  /-- Address of the coordinate offset supplied by a record or packet. -/
  offsetAddr : ℕ
  /-- Actual value of the offset at that address. -/
  offset : ℕ
  /-- First word of the public vector of digit addresses. -/
  digitsAddr : ℕ
  /-- Raw bit addresses and actual values, highest significance first. -/
  digits : List (ℕ × Bool)
  /-- Address of the binary place in the delivered unary descriptor, or a zero word. -/
  placeAddr : ℕ
  /-- Actual value of that delivered place. -/
  place : ℕ

/-- Coordinate and increment of an instantiated native record. -/
def Operand.pair (o : Operand) : ℕ × ℕ :=
  (o.base+o.offset, readDigits 0 (o.digits.map Prod.snd) * 2^o.place)

variable {w : ℕ}

/-- Both words read by each indirect bit probe have the designated values. -/
def digitRefsAt (m : Memory w) : ℕ → List (ℕ × Bool) → Prop
  | _, [] => True
  | p, (a,b)::xs => (m p).val = a ∧ (m a).val = b.toNat ∧ digitRefsAt m (p+1) xs

/-- Physical five-word descriptor and the data reached by its pointers. -/
def Operand.resident (o : Operand) (m : Memory w) (p : ℕ) : Prop :=
  (m p).val = o.base ∧ (m (p+1)).val = o.offsetAddr ∧ (m o.offsetAddr).val = o.offset ∧
  (m (p+2)).val = o.digitsAddr ∧ (m (p+3)).val = o.digitsAddr+o.digits.length ∧
  (m (p+4)).val = o.placeAddr ∧ (m o.placeAddr).val = o.place ∧
  digitRefsAt m o.digitsAddr o.digits

/-- Exact natural output in the machine word, including its place computation. -/
def Operand.fits (o : Operand) (w : ℕ) : Prop :=
  o.pair.1 < 2^w ∧ o.place < w ∧ o.pair.2 < 2^w

/-- Load all five fields, gather the dynamic coordinate offset and shift, and advance
the public descriptor cursor by one row. -/
def loadOperand : Code := .block [
  .load 48 40, .binary .add 40 40 63, .load 56 40, .load 56 56, .binary .add 48 48 56,
  .binary .add 40 40 63, .load 50 40, .binary .add 40 40 63, .load 52 40,
  .binary .add 40 40 63, .load 49 40, .load 49 49, .binary .add 40 40 63, .constant 55 0]

/-- Write the coordinate and its shifted increment to adjacent output words. -/
def emitPair : Code := .block [.binary .shiftLeft 55 55 49, .store 42 48,
  .binary .add 42 42 63, .store 42 55, .binary .add 42 42 63]

/-- Process one physical descriptor into the scatter routine's exact wire format. -/
def body : Code := .seq loadOperand (.seq gather emitPair)

/-- The descriptor region is in registers 40 and 41. Register 42 addresses the first
output word. The cursor advances by five input words and two output words per record. -/
def loop : Code := .whileLt 40 41 body

/-- Load the input descriptor pointer from slot 44, the number of records from 35, and
the destination array from 34. This table does not depend on the parsed batch. -/
def setup : Code := .block [readFrame 40 60 61 44,
  readFrame 41 60 61 35, readFrame 42 60 61 34,
  .constant 63 1, .constant 57 5, .binary .mul 41 41 57, .binary .add 41 40 41]

/-- The entry after private calls and before the native tally's scatter loop. -/
def materialize : Code := .seq setup loop

/-- Registers maintained at the start of each outer iteration. -/
def ready (s : Bank w) (p stop dst : ℕ) : Prop :=
  (s 40).val = p ∧ (s 41).val = stop ∧ (s 42).val = dst ∧ (s 63).val = 1

/-- Physical memory after a single generated scatter record. -/
def storePair (m : Memory w) (p : ℕ) (r : ℕ × ℕ) : Memory w :=
  Function.update (Function.update m p (word w r.1)) (p+1) (word w r.2)

private theorem digitsAt_of_refsAt (m : Memory w) (p : ℕ) (xs : List (ℕ × Bool))
    (h : digitRefsAt m p xs) : DigitsAt m p (xs.map Prod.snd) := by
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨a,b⟩ := x
    exact ⟨by rw [h.1]; exact h.2.1, ih _ h.2.2⟩

set_option maxRecDepth 4000 in
private theorem load_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (o : Operand) (p stop dst : ℕ) (hs : ready s p stop dst)
    (hr : o.resident m p) (hptr : p+5 < 2^w) (hf : o.fits w) :
    ∃ es t, Runs pub mac loadOperand s m es t m ∧ traceCost es ≤ loadOperand.slots ∧
      ready t (p+5) stop dst ∧ (t 48).val = o.pair.1 ∧ (t 49).val = o.place ∧
      (t 50).val = o.digitsAddr ∧ (t 52).val = o.digitsAddr+o.digits.length ∧ (t 55).val = 0 := by
  obtain ⟨h40,h41,h42,h63⟩ := hs
  obtain ⟨hbase,hOffsetAddr,hOffset,hDigits,hDigitsEnd,hPlaceAddr,hPlace,_⟩ := hr
  have hcoord : o.base+o.offset < 2^w := hf.1
  have safe : loadOperand.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [loadOperand,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,
      addressOpFits,addressOp,readings,h40,h63,hbase,hOffsetAddr,hOffset,hcoord]
    omega
  obtain ⟨es,t,r,hc,ht⟩ := Code.runReadOnly loadOperand pub mac m s safe
  refine ⟨es,t,r,hc,?_⟩
  change (readings t 40 = _ ∧ readings t 41 = _ ∧ readings t 42 = _ ∧ readings t 63 = _) ∧
    readings t 48 = _ ∧ readings t 49 = _ ∧ readings t 50 = _ ∧ readings t 52 = _ ∧ readings t 55 = _
  rw [ht]
  simp [loadOperand,Code.block,Code.evalNat,Function.update,addressOp,readings,h40,h41,h42,h63,
    hbase,hOffsetAddr,hOffset,hDigits,hDigitsEnd,hPlaceAddr,hPlace,Operand.pair]

private theorem emit_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (o : Operand) (p stop dst : ℕ) (hs : ready s p stop dst)
    (hcoord : (s 48).val = o.pair.1) (hplace : (s 49).val = o.place)
    (hval : (s 55).val = readDigits 0 (o.digits.map Prod.snd))
    (hdst : dst+2 < 2^w) (hf : o.fits w) :
    ∃ es t, Runs pub mac emitPair s m es t (storePair m dst o.pair) ∧ traceCost es = 5 ∧
      ready t p stop (dst+2) := by
  obtain ⟨h40,h41,h42,h63⟩ := hs
  have h48 : s 48 = word w o.pair.1 := Fin.ext (hcoord.trans (word_val _ _ hf.1).symm)
  have shift : BinaryOp.shiftLeft.eval (s 55) (s 49) = word w o.pair.2 := by
    simp [BinaryOp.eval,hplace,hf.2.1,Nat.shiftLeft_eq,hval,Operand.pair,word]
  have hd1 : (s 42+s 63).val = dst+1 := by rw [Fin.val_add,h42,h63,Nat.mod_eq_of_lt (by omega)]
  have hd2 : (s 42+s 63+s 63).val = dst+2 := by rw [Fin.val_add,hd1,h63,Nat.mod_eq_of_lt (by omega)]
  let e := effect false s m emitPair
  have r := effect_runs pub mac false s m emitPair (by decide)
  change Runs pub mac emitPair s m e.trace e.bank e.mem at r
  have hm : e.mem = storePair m dst o.pair := by
    change Function.update (Function.update m (s 42).val (s 48)) (s 42+s 63).val
      (BinaryOp.shiftLeft.eval (s 55) (s 49)) = storePair m dst o.pair
    rw [h42,h48,hd1,shift]
    rfl
  rw [hm] at r
  refine ⟨_,_,r,?_,?_⟩
  · rw [DiagonalTallyRAM.ordinary_cost (by decide) r]; rfl
  · simp [ready,e,emitPair,Code.block,effect,Function.update,BinaryOp.eval,h40,h41,h63,hd2]

/-- One materialized record has the exact integer coordinate and increment from
the delivered words and private bits. -/
theorem body_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (o : Operand) (p stop dst : ℕ) (hs : ready s p stop dst)
    (hr : o.resident m p) (hf : o.fits w) (hptr : p+5 < 2^w) (hdst : dst+2 < 2^w) :
    ∃ es t, Runs pub mac body s m es t (storePair m dst o.pair) ∧
      traceCost es ≤ 20+8*o.digits.length ∧ ready t (p+5) stop (dst+2) := by
  obtain ⟨a,t,ra,ha,rt,t48,t49,t50,t52,t55⟩ := load_runs pub mac s m o p stop dst hs hr hptr hf
  have hv : readDigits 0 (o.digits.map Prod.snd) < 2^w := by
    apply lt_of_le_of_lt _ hf.2.2
    apply Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  obtain ⟨b,u,rb,hb,_,u55,pr⟩ := gather_runs pub mac t m (o.digits.map Prod.snd)
    o.digitsAddr 0 _ t50 t55 t52 rt.2.2.2 (by simp) (digitsAt_of_refsAt m _ _ hr.2.2.2.2.2.2.2) hv
  have ru : ready u (p+5) stop dst := by
    simpa only [ready,pr 40 (by decide) (by decide) (by decide),
      pr 41 (by decide) (by decide) (by decide),pr 42 (by decide) (by decide) (by decide),
      pr 63 (by decide) (by decide) (by decide)] using rt
  obtain ⟨c,z,rc,hc,rz⟩ := emit_runs pub mac u m o _ stop dst ru
    ((congrArg Fin.val (pr 48 (by decide) (by decide) (by decide))).trans t48)
    ((congrArg Fin.val (pr 49 (by decide) (by decide) (by decide))).trans t49) u55 hdst hf
  refine ⟨_,z,ra.seq (rb.seq rc),?_,rz⟩
  unfold traceCost
  simp only [VPVNP.RAMBuckets.cost_append]
  change traceCost a+(traceCost b+traceCost c) ≤ _
  simp only [List.length_map] at hb
  have hl : loadOperand.slots = 14 := by decide
  omega

end DiagonalTallyMaterialize

end BorderVNP
end Computability
end OAI
