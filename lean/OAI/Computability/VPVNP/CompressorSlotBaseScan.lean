import OAI.Computability.VPVNP.CompressorSlotBasePass
import OAI.Computability.VPVNP.CompressorSlotBaseLookup
import OAI.Computability.VPVNP.CompressorSlotOwnerRuns

/-!
# Native scan of packed base arcs

Each call starts at one packed base and outgoing slot. Two reads follow the
lane-zero source row to its adjacent incoming field in the inverse table.
The worker strips the incoming side and lane digits, writes the base target
and lane displacement to separate arrays, and advances its persistent cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotBaseScan

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

private abbrev divWord := @BinaryOp.eval w .div
private abbrev modWord := @BinaryOp.eval w .mod

/-- The public words, in order, are the degree, number of lanes, row-table base,
inverse-table base, base-target output address, and displacement output address. -/
def code : List (Op 10 6) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1, .constant 3 2, .constant 4 1,
   .binary .div 5 0 1, .binary .mod 6 0 1, .binary .mul 5 5 2, .binary .mul 5 5 3,
   .binary .mul 5 5 1, .binary .add 5 5 6, .publicWord 6 2, .binary .add 6 6 5, .read 5 6,
   .binary .add 5 5 4, .publicWord 6 3, .binary .add 6 6 5, .read 5 6,
   .binary .mod 6 5 1, .binary .div 5 5 1, .binary .div 5 5 3, .binary .mod 7 5 2,
   .binary .div 5 5 2, .binary .mul 5 5 1, .binary .add 5 5 6,
   .publicWord 8 4, .binary .add 8 8 0, .write 8 5,
   .publicWord 9 5, .binary .add 9 9 0, .write 9 7, .binary .add 0 0 4]

/-- Row of the outgoing slot over lane zero. -/
def srcRect (p : Fin 6 → Word w) (i : Word w) : Word w :=
  divWord i (p 0) * p 1 * 2 * p 0 + modWord i (p 0)

/-- Address of the outgoing endpoint field in the row table at lane zero for the given base
port. -/
def rowAddr (p : Fin 6 → Word w) (i : Word w) : Word w := p 2 + srcRect p i

/-- Address in the inverse table of the incoming field paired with the source field read at
lane zero. -/
def invAddr (p : Fin 6 → Word w) (m : Memory w) (i : Word w) : Word w :=
  p 3 + (m (rowAddr p i).val + 1)

/-- Incoming rectangular slot of the same arc. -/
def dstRect (p : Fin 6 → Word w) (m : Memory w) (i : Word w) : Word w :=
  m (invAddr p m i).val

/-- Recover the target site index from the incoming rectangular slot by removing the slot and
side digits. -/
def dstSite (p : Fin 6 → Word w) (m : Memory w) (i : Word w) : Word w :=
  divWord (divWord (dstRect p m i) (p 0)) 2

/-- Base index and incoming slot, encoded in the same radix as the source cursor. -/
def target (p : Fin 6 → Word w) (m : Memory w) (i : Word w) : Word w :=
  divWord (dstSite p m i) (p 1) * p 0 + modWord (dstRect p m i) (p 0)

/-- Residual lane of the target reached from source lane zero, giving the base arc's lane
displacement. -/
def displacement (p : Fin 6 → Word w) (m : Memory w) (i : Word w) : Word w :=
  modWord (dstSite p m i) (p 1)

/-- Trace of one base-port visit, reading the row and inverse tables before writing the target
base port and lane displacement. -/
def events (p : Fin 6 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  List.replicate 13 .tick ++ [.read (rowAddr p i) (m (rowAddr p i).val)] ++
    List.replicate 3 .tick ++ [.read (invAddr p m i) (dstRect p m i)] ++
    List.replicate 9 .tick ++ [.write (p 4+i) (target p m i), .tick, .tick,
      .write (p 5+i) (displacement p m i), .tick]

theorem events_after (p : Fin 6 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) =
      writeMemory (writeMemory m (p 4+i) (target p m i)) (p 5+i) (displacement p m i) := rfl

theorem events_work (p : Fin 6 → Word w) (m : Memory w) (i : Word w) :
    countProbes (events p m i) = 4 ∧ (events p m i).length = 32 := ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The two lookups precede both writes, so the words in the trace are computed
from the memory at the start of the call, even if some addresses coincide. -/
theorem native (p : Fin 6 → Word w) (m : Memory w) (i : Word w) :
    let M := (template code 0).instantiate w p
    execute M.program 33 (M.program.start i) m [] = some ⟨events p m i, some (i+1)⟩ := by
  change execute ((template code 0).instantiate w p).program (1+code.length)
    ⟨_, i, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  rfl

/-- Worst-case word operations, including arbitrary shortened read streams. -/
theorem opcode_work (p : Fin 6 → Word w) (i : Word w) (allowance : ℕ) (bits : List Bool) :
    let M := (template code 0).instantiate w p
    M.loggedDispatchWork 33 (M.logProgram.start i) allowance bits ≤ 198 :=
  SlotOwners.template_opcode_work code 0 p 33 _ allowance bits

private theorem word_add (base : Word w) (i : ℕ) :
    base + Fin.ofNat _ i = Fin.ofNat _ (base.val+i) := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]

private theorem word_succ (i : ℕ) :
    (Fin.ofNat (2^w) i : Word w) + 1 = Fin.ofNat _ (i+1) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]

/-- Each table lookup falls outside the two output regions. The inverse address
is specified using the field returned by the original row-table read. -/
def ReadsOutside (p : Fin 6 → Word w) (m : Memory w) (count : ℕ) : Prop :=
  ∀ i < count, ∀ a ∈ [rowAddr p (Fin.ofNat _ i), invAddr p m (Fin.ofNat _ i)],
    (a.val < (p 4).val ∨ (p 4).val+count ≤ a.val) ∧
    (a.val < (p 5).val ∨ (p 5).val+count ≤ a.val)

/-- Fill both base-graph tables using two reads and two writes per arc.
The two output arrays may be placed in either order. -/
theorem run (p : Fin 6 → Word w) (initial : Memory w) (count : ℕ)
    (fit₁ : (p 4).val+count ≤ 2^w) (fit₂ : (p 5).val+count ≤ 2^w)
    (disjoint : (p 4).val+count ≤ (p 5).val ∨ (p 5).val+count ≤ (p 4).val)
    (reads : ReadsOutside p initial count) :
    let P := ((template code 0).instantiate w p).program
    ∃ rs, SlotBasePass.FilledRun P 33 4 32 (p 4).val (p 5).val count
      (fun i => target p initial (Fin.ofNat _ i)) (fun i => displacement p initial (Fin.ofNat _ i))
      initial rs := by
  intro P
  apply SlotBasePass.run P 33 4 32 (p 4).val (p 5).val count _ _ initial fit₁ fit₂ disjoint
  intro i hi mem frame
  let j : Word w := Fin.ofNat _ i
  have eq (a : Word w) (ha : a ∈ [rowAddr p j, invAddr p initial j]) :
      mem a.val = initial a.val := by
    obtain ⟨h₁, h₂⟩ := reads i hi a ha
    exact frame a.val (by omega) (by omega)
  have row := eq (rowAddr p j) (by simp)
  have sameInv : invAddr p mem j = invAddr p initial j := by simp only [invAddr, row]
  have dst : dstRect p mem j = dstRect p initial j := by
    simpa only [dstRect, sameInv] using eq (invAddr p initial j) (by simp)
  refine ⟨events p mem j, ?_, ?_, (events_work ..).1, (events_work ..).2⟩
  · rw [native, word_succ]
  · rw [events_after]
    simp only [target, displacement, dstSite, dst, j, word_add]

private theorem div_val (x y : Word w) : (divWord x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem mod_val (x y : Word w) : (modWord x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)

/-- The native mixed-radix address equals the lane-zero row when it fits. -/
theorem srcRect_val (p : Fin 6 → Word w) (i : Word w) (hw : 2 < 2^w)
    (fit : SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val < 2^w) :
    (srcRect p i).val = SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val := by
  have two : (2 : Word w).val = 2 := Nat.mod_eq_of_lt hw
  simp only [srcRect, Fin.val_add, Fin.val_mul, div_val, mod_val, two,
    Nat.mod_mul_mod, Nat.mod_add_mod]
  exact Nat.mod_eq_of_lt fit

/-- Both word addresses denote the ordinary natural-number table lookups. -/
theorem read_addresses (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (hw : 2 < 2^w)
    (rowFit : (p 2).val + SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val < 2^w)
    (invFit : let source := SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val
              (p 3).val + ((m ((p 2).val+source)).val+1) < 2^w) :
    let source := SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val
    let field := m ((p 2).val+source)
    (rowAddr p i).val = (p 2).val+source ∧ (invAddr p m i).val = (p 3).val+(field.val+1) := by
  intro source field
  have hr : (rowAddr p i).val = (p 2).val+source := by
    rw [rowAddr, Fin.val_add, srcRect_val _ _ hw (by omega), Nat.mod_eq_of_lt rowFit]
  have hi : (p 3).val + (field.val+1) < 2^w := invFit
  have hI : (invAddr p m i).val = (p 3).val + (field.val+1) := by
    change (p 3 + (m (rowAddr p i).val+1)).val = _
    rw [hr]
    change (p 3 + (field+1)).val = _
    rw [Fin.val_add, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2^w),
      Nat.mod_eq_of_lt (by omega : field.val+1 < 2^w), Nat.mod_eq_of_lt hi]
  exact ⟨hr, hI⟩

/-- With fitting input addresses the words computed by the worker agree with
the numerical lane-zero lookup and incoming-slot decoder. -/
theorem outputs_eq (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (hw : 2 < 2^w)
    (rowFit : (p 2).val + SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val < 2^w)
    (invFit : let source := SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val
              (p 3).val + ((m ((p 2).val+source)).val+1) < 2^w) :
    let source := SlotSchedule.laneZeroRow (p 0).val (p 1).val i.val
    let field := m ((p 2).val+source)
    let result := SlotSchedule.unpackBaseTarget (p 0).val (p 1).val (m ((p 3).val+(field.val+1))).val
    target p m i = Fin.ofNat _ result.1 ∧ displacement p m i = Fin.ofNat _ result.2 := by
  intro source field result
  have hI : (invAddr p m i).val = (p 3).val+(field.val+1) :=
    (read_addresses p m i hw rowFit invFit).2
  have two : (2 : Word w).val = 2 := Nat.mod_eq_of_lt hw
  constructor <;> apply Fin.ext <;>
    simp only [result, SlotSchedule.unpackBaseTarget, target, displacement, dstSite, dstRect, hI,
      div_val, mod_val, two, Fin.val_mul, Fin.val_add, Fin.val_ofNat, Nat.mod_add_mod]
  exact (Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt ((Nat.div_le_self ..).trans_lt
    ((Nat.div_le_self ..).trans_lt (m ((p 3).val+(field.val+1))).isLt)))).symm

end CompressorRecords.SlotBaseScan

end VPVNP
end Computability
end OAI
