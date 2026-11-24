import OAI.Computability.VPVNP.LiveExponentDigits
import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMRecords

/-!
# Native burst RAM digit calls for the live exponent update

The persistent word indexes the flattened exponent array. Public words
designate the incoming bit array, outgoing bit array, increment array,
digit width and total digit count, respectively. The increment array
initially holds the nominated grammar counts followed by the gadget
counts. Its entry for a label doubles as that label's carry. Each call
uses four external probes regardless of the length of an exponent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- A native digit-update operation over sixteen registers and five public operands. -/
abbrev DigitOp := Op 16 5

/-- Register zero is the digit cursor and register one receives its successor.
Registers 2, 3, 4 hold incoming, outgoing and carry addresses. Registers 5, 6, 7
hold their loaded values. Registers 8 and 9 hold the total and next carry.
The last bit of each label additionally requires the carry to vanish. -/
def digitOps : List DigitOp :=
  [.stateWord 0, .publicWord 10 3, .publicWord 2 0, .binary .add 2 2 0,
   .read 5 2, .publicWord 3 1, .binary .add 3 3 0, .read 6 3,
   .binary .div 11 0 10, .publicWord 4 2, .binary .add 4 4 11, .read 7 4,
   .constant 12 2, .guardLt 5 12, .binary .add 8 7 5,
   .binary .mod 11 8 12, .guardEq 6 11, .binary .div 9 8 12,
   .constant 13 1, .binary .mod 11 0 10, .binary .add 11 11 13,
   .binary .div 11 11 10, .binary .mul 11 11 9, .constant 14 0,
   .guardEq 11 14, .write 4 9, .binary .add 1 0 13]

variable {w : ℕ}

/-- Address of the incoming cut bit at the flattened digit cursor. -/
def incomingAddress (pub : Fin 5 → Word w) (s : Word w) := pub 0 + s

/-- Address of the proposed outgoing cut bit at the flattened digit cursor. -/
def outgoingAddress (pub : Fin 5 → Word w) (s : Word w) := pub 1 + s

/-- Address of the current label's increment word, used as the carry during its digit scan. -/
def carryAddress (pub : Fin 5 → Word w) (s : Word w) :=
  pub 2 + BinaryOp.div.eval s (pub 3)

private def sumWord (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :=
  m (carryAddress pub s).val + m (incomingAddress pub s).val

private def lastMask (pub : Fin 5 → Word w) (s : Word w) :=
  BinaryOp.div.eval ((BinaryOp.mod.eval s (pub 3)) + Fin.ofNat (2^w) (1 : Word 2).val) (pub 3)

private def carryWord (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :=
  BinaryOp.div.eval (sumWord pub s m) 2

private def NativeTest (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Prop :=
  m (incomingAddress pub s).val < 2 ∧
    m (outgoingAddress pub s).val = BinaryOp.mod.eval (sumWord pub s m) 2 ∧
    lastMask pub s * carryWord pub s m = 0

private instance (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Decidable (NativeTest pub s m) := by
  unfold NativeTest
  infer_instance

/-- Exact event stream of a successful digit block, including its three
memory reads and its single write. -/
def digitEvents (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : List (Event w) :=
  [.tick, .tick, .tick, .tick, .read (incomingAddress pub s) (m (incomingAddress pub s).val),
   .tick, .tick, .read (outgoingAddress pub s) (m (outgoingAddress pub s).val),
   .tick, .tick, .tick, .read (carryAddress pub s) (m (carryAddress pub s).val),
   .tick, .tick, .tick, .tick, .tick, .tick, .tick, .tick, .tick, .tick,
   .tick, .tick, .tick, .write (carryAddress pub s) (carryWord pub s m), .tick]

theorem digitEvents_counts (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    (digitEvents pub s m).length = 27 ∧ countProbes (digitEvents pub s m) = 4 ∧
      choiceBits (digitEvents pub s m) = [] := by
  exact ⟨rfl, rfl, rfl⟩

theorem after_digitEvents (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    after m (digitEvents pub s m) = writeMemory m (carryAddress pub s) (carryWord pub s m) := rfl

private theorem digit_trace_pass (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (regs : Regs w 16) (ht : NativeTest pub s m) :
    ∃ rs, trace pub s digitOps regs m = some (digitEvents pub s m, rs,
      writeMemory m (carryAddress pub s) (carryWord pub s m)) ∧ rs 1 = s+1 := by
  rcases ht with ⟨ha,hb,hc⟩
  simp (config := { decide := true }) [incomingAddress, outgoingAddress, carryAddress,
    sumWord, carryWord, lastMask, BinaryOp.eval] at ha hb hc
  simp (config := { decide := true }) [digitOps, trace, Op.effect, Function.update,
    BinaryOp.eval, ha, hb, hc, digitEvents, incomingAddress, outgoingAddress,
    carryAddress, sumWord, carryWord]
  rfl

private theorem digit_trace_fail (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (regs : Regs w 16) (ht : ¬NativeTest pub s m) :
    trace pub s digitOps regs m = none := by
  by_cases ha : m (incomingAddress pub s).val < 2
  · by_cases hb : m (outgoingAddress pub s).val = BinaryOp.mod.eval (sumWord pub s m) 2
    · have hc : lastMask pub s * carryWord pub s m ≠ 0 := fun e => ht ⟨ha, hb, e⟩
      simp (config := { decide := true }) [incomingAddress, outgoingAddress, carryAddress,
        sumWord, carryWord, lastMask, BinaryOp.eval] at ha hb hc
      simp (config := { decide := true }) [digitOps, trace, Op.effect, Function.update,
        BinaryOp.eval, ha, hb, hc]
    · simp (config := { decide := true }) [incomingAddress, outgoingAddress, carryAddress,
        sumWord, BinaryOp.eval] at ha hb
      simp (config := { decide := true }) [digitOps, trace, Op.effect, Function.update, BinaryOp.eval, ha, hb]
  · change ¬m (pub 0 + s).val < 2 at ha
    simp (config := { decide := true }) [digitOps, trace, Op.effect, Function.update, BinaryOp.eval, ha]

/-- The extra entry test ends the stage at cursor `t * Z`. Each prior call
executes one copy of the same digit block and returns cursor plus one. -/
def digitTemplate : Template 34 16 5 where
  literalWidth := 2
  entry := 29
  code i := if h : i.val < digitOps.length then
      (digitOps[i.val]).emit ⟨i.val+1, by have : digitOps.length = 27 := rfl; omega⟩ 28
    else if i = 27 then .returnState 1
    else if i = 29 then .stateWord 0 30
    else if i = 30 then .publicWord 15 4 31
    else if i = 31 then .jumpLt 0 15 0 32
    else if i = 32 then .jumpEq 0 15 33 28
    else if i = 33 then .accept
    else .reject

private theorem indexedContains {p r k : ℕ} (M : Machine w p r k) (bad : Fin p)
    (ops : List (Op r k)) (pc : Fin (ops.length+1) → Fin p)
    (hc : ∀ i : Fin ops.length, M.code (pc i.castSucc) =
      (ops[i.val].emit (pc i.succ) bad).resize w) :
    Contains M bad (pc 0) ops (pc (Fin.last ops.length)) := by
  induction ops with
  | nil => exact .nil _
  | cons o ops ih =>
    apply Contains.cons (next := pc (⟨0, by simp⟩ : Fin (o :: ops).length).succ) (hc ⟨0, by simp⟩)
    exact ih (fun i => pc i.succ) (fun i => hc i.succ)

private theorem contains_digit (pub : Fin 5 → Word w) :
    Contains (digitTemplate.instantiate w pub) 28 0 digitOps 27 := by
  apply indexedContains _ _ _ (fun i => ⟨i.val, by have := i.isLt; change _ < 28 at this; omega⟩)
  intro i
  simp [digitTemplate, Template.instantiate, i.isLt]

/-- Native report of one successful call, including its entry instructions. -/
def digitReport (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Report w :=
  ⟨.tick :: .tick :: .tick :: digitEvents pub s m, some (s+1)⟩

theorem digitReport_cost (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    (digitReport pub s m).probes = 4 ∧ (digitReport pub s m).events.length = 30 ∧
      choiceBits (digitReport pub s m).events = [] := ⟨rfl, rfl, rfl⟩

theorem digitReport_after (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    after m (digitReport pub s m).events = writeMemory m (carryAddress pub s) (carryWord pub s m) := rfl

private theorem execute_entry (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (f : ℕ) (hs : s < pub 4) :
    let M := digitTemplate.instantiate w pub
    let regs : Regs w 16 := Function.update (Function.update (fun _ => 0) 0 s) 15 (pub 4)
    execute M.program (f+3) (M.program.start s) m bs =
      (execute M.program f ⟨0, s, regs, fun _ => 0⟩ m bs).map
        (fun r => r.prepend .tick |>.prepend .tick |>.prepend .tick) := by
  dsimp only
  simp (config := { decide := true }) [execute, Machine.program, digitTemplate, Template.instantiate,
    Instr.resize, Instr.run, Config.put, Function.update, hs, Option.map_map, Function.comp_def]

private theorem execute_block (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (regs : Regs w 16) (bs : List Bool) (f : ℕ) :
    let M := digitTemplate.instantiate w pub
    execute M.program (f+28) ⟨0,s,regs,fun _ => 0⟩ m bs =
      (trace pub s digitOps regs m).bind fun (es, rs, _) =>
        if bs = [] then some ⟨es, some (rs 1)⟩ else none := by
  dsimp only
  have h := (contains_digit pub).execute (by rfl) s regs (fun _ => 0) m bs (f+1)
  rw [show f+28 = f+1+digitOps.length by rfl, h, run_eq_trace]
  congr 1
  funext z
  obtain ⟨es, rs, mem⟩ := z
  change ((execute (digitTemplate.instantiate w pub).program (f+1) ⟨27,s,rs,fun _ => 0⟩ mem bs).map _) = _
  simp (config := { decide := true }) [execute, digitTemplate, Template.instantiate, Machine.program,
    Instr.resize, Instr.run]

private theorem execute_digit (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (f : ℕ) (hs : s < pub 4) :
    execute (digitTemplate.instantiate w pub).program (f+31)
      ((digitTemplate.instantiate w pub).program.start s) m bs =
      if NativeTest pub s m ∧ bs = [] then some (digitReport pub s m) else none := by
  classical
  rw [show f+31 = (f+28)+3 by omega, execute_entry pub s m bs _ hs, execute_block]
  by_cases ht : NativeTest pub s m
  · obtain ⟨rs, hr, hv⟩ := digit_trace_pass pub s m (Function.update (Function.update (fun _ => 0) 0 s) 15 (pub 4)) ht
    simp only [hr, Option.bind_some, hv, ht, true_and]
    by_cases hb : bs = [] <;> simp [hb, digitReport, Report.prepend]
  · simp [digit_trace_fail pub s m _ ht, ht]

/-- The completed stage accepts with exactly four entry ticks and no choices. -/
theorem execute_done (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (f : ℕ) (hs : s = pub 4) :
    execute (digitTemplate.instantiate w pub).program (f+5)
      ((digitTemplate.instantiate w pub).program.start s) m bs =
      if bs = [] then some ⟨[.tick, .tick, .tick, .tick], none⟩ else none := by
  subst s
  simp (config := { decide := true }) [execute, Machine.program, digitTemplate, Template.instantiate,
    Instr.resize, Instr.run, Config.put, Function.update]
  split <;> simp [Report.prepend]

/-- Ordinary integer addition, phrased using the natural values of the cells
read by one call. The final bit of each label also checks for overflow. -/
def DigitTest (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Prop :=
  let x := (m (incomingAddress pub s).val).val
  let y := (m (outgoingAddress pub s).val).val
  let c := (m (carryAddress pub s).val).val
  x < 2 ∧ y = (c+x)%2 ∧ (s.val % (pub 3).val + 1 = (pub 3).val → (c+x)/2 = 0)

private instance (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Decidable (DigitTest pub s m) := by
  unfold DigitTest
  infer_instance

private theorem val_div (x y : Word w) : (BinaryOp.div.eval x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) x.isLt)

private theorem val_mod (x y : Word w) : (BinaryOp.mod.eval x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le ..) x.isLt)

private theorem two_val (hw : 2 ≤ w) : (2 : Word w).val = 2 :=
  Nat.mod_eq_of_lt (lt_of_lt_of_le (show 2 < 2^2 by decide) (Nat.pow_le_pow_right (by decide) hw))

private theorem lastMask_val (pub : Fin 5 → Word w) (s : Word w) (hz : 0 < (pub 3).val) :
    (lastMask pub s).val = if s.val % (pub 3).val + 1 = (pub 3).val then 1 else 0 := by
  have hj := Nat.mod_lt s.val hz
  have hf : s.val % (pub 3).val + 1 < 2^w := (Nat.succ_le_of_lt hj).trans_lt (pub 3).isLt
  rw [lastMask, val_div]
  change ((BinaryOp.mod.eval s (pub 3)) + 1 : Word w).val / (pub 3).val = _
  rw [Fin.val_add_one_of_lt', val_mod]
  · split
    · rename_i he
      rw [he, Nat.div_self hz]
    · rename_i hn
      exact Nat.div_eq_of_lt (by omega)
  · rw [val_mod]
    exact hf

theorem carryWord_val (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) (hw : 2 ≤ w)
    (hfit : (m (carryAddress pub s).val).val + (m (incomingAddress pub s).val).val < 2^w) :
    (carryWord pub s m).val =
      ((m (carryAddress pub s).val).val + (m (incomingAddress pub s).val).val) / 2 := by
  rw [carryWord, val_div, two_val hw, sumWord, Fin.val_add, Nat.mod_eq_of_lt hfit]

private theorem nativeTest_iff (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (hw : 2 ≤ w) (hz : 0 < (pub 3).val)
    (hfit : (m (carryAddress pub s).val).val + (m (incomingAddress pub s).val).val < 2^w) :
    NativeTest pub s m ↔ DigitTest pub s m := by
  have hc := carryWord_val pub s m hw hfit
  have hmask := lastMask_val pub s hz
  have ho : (BinaryOp.mod.eval (sumWord pub s m) 2).val =
      ((m (carryAddress pub s).val).val + (m (incomingAddress pub s).val).val) % 2 := by
    rw [val_mod, two_val hw, sumWord, Fin.val_add, Nat.mod_eq_of_lt hfit]
  unfold NativeTest DigitTest
  rw [Fin.lt_def, two_val hw, Fin.ext_iff, ho]
  by_cases he : s.val % (pub 3).val + 1 = (pub 3).val
  · have one_val : (1 : Word w).val = 1 :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le (by decide : 1 < 2^2) (Nat.pow_le_pow_right (by decide) hw))
    have hm : lastMask pub s = 1 := Fin.ext (by rw [one_val]; simpa only [he, ite_true] using hmask)
    rw [hm, one_mul, Fin.ext_iff, hc]
    simp [he]
  · have hm : lastMask pub s = 0 := Fin.ext (by simpa [he] using hmask)
    simp [hm, he]

/-- Every well-sized nonterminal call has exactly the branch stream and report
specified by the arithmetic test. The fuel bound counts the final return. -/
theorem execute_digit_iff (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (hw : 2 ≤ w) (hz : 0 < (pub 3).val) (hs : s < pub 4)
    (hfit : (m (carryAddress pub s).val).val + (m (incomingAddress pub s).val).val < 2^w)
    (bs : List Bool) (f : ℕ) :
    execute (digitTemplate.instantiate w pub).program (f+31)
      ((digitTemplate.instantiate w pub).program.start s) m bs =
      if DigitTest pub s m ∧ bs = [] then some (digitReport pub s m) else none := by
  rw [execute_digit pub s m bs f hs]
  by_cases h : DigitTest pub s m
  · simp [(nativeTest_iff pub s m hw hz hfit).mpr h, h]
  · simp [mt (nativeTest_iff pub s m hw hz hfit).mp h, h]

/-- Every successful nonterminal call consumes an empty choice stream and
returns the next cursor, including on arbitrary initial memory. -/
theorem data_result {pub : Fin 5 → Word w} {s : Word w} {m : Memory w}
    {bs : List Bool} {f : ℕ} {r : Report w} (hs : s < pub 4)
    (hr : execute (digitTemplate.instantiate w pub).program (f+31)
      ((digitTemplate.instantiate w pub).program.start s) m bs = some r) :
    bs = [] ∧ r = digitReport pub s m := by
  rw [execute_digit pub s m bs f hs] at hr
  split at hr
  · rename_i h
    exact ⟨h.2, (Option.some.inj hr).symm⟩
  · contradiction

end LiveExponent

end VPVNP
end Computability
end OAI
