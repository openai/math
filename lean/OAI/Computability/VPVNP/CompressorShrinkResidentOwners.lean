import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorSlotOwnerAgreement
import OAI.Computability.VPVNP.ShrinkRoles

/-!
# Native generation of the shrinking resident owner columns

A history cursor combines its motif number with either a party ordinal or an
absorbed edge type. The worker uses the sorted absolute-CD column and the
selected layout's A/B/D role words to write the owner at that cursor. It needs
two memory reads and one write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ResidentOwners

open Compression Compression.ShrinkMotif BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open PhaseRecipe BlockPlanner
open scoped Fin.CommRing

/-- The six map parties or four absorbed edge types stored per motif. -/
def arity (maps : Bool) := if maps then 6 else 4

variable {w : ℕ}

private def four : Word w := 2*2
private def radix (maps : Bool) : Word w := (if maps then 3 else 2)*2

private theorem four_eq : (four : Word w) = 4 := by unfold four; norm_num
private theorem radix_eq (maps : Bool) : (radix maps : Word w) = (arity maps : Word w) := by
  cases maps <;> norm_num [radix,arity]

private def mux (flag lo hi : Word w) := lo + flag*(hi-lo)

private def chooseReg (flag lo hi dst : Fin 20) : List (Op 20 4) :=
  [.binary .sub 15 hi lo,.binary .mul 15 flag 15,.binary .add dst lo 15]

/-- Registers 11, 12 and 13 carry the three bits of the within-motif tag.
Register 8 carries the layout, register 9 is two, and register 14 is the
resulting role offset. -/
private def roleOps (maps : Bool) : List (Op 20 4) := if maps then
  chooseReg 11 8 9 16 ++ chooseReg 12 11 16 14 ++
    [.binary .mul 16 9 8,.binary .sub 17 9 8] ++ chooseReg 11 16 17 18 ++ chooseReg 13 14 18 14
  else [.binary .mul 16 11 12] ++ chooseReg 16 8 9 14

/-- Native owner-scan instructions for a hidden field or party map. Decode the occurrence, read
its absolute CD identifier and role word, and write the packed owner. -/
def code (maps : Bool) : List (Op 20 4) :=
  [.stateWord 0,.constant 9 2,.binary .mul 10 9 9,
   .constant 3 (if maps then 3 else 2),.binary .mul 3 3 9,.binary .div 1 0 3,.binary .mod 2 0 3,
   .publicWord 8 2,
   .binary .mod 11 2 9,.binary .div 12 2 9,.binary .mod 12 12 9,.binary .div 13 2 10] ++
  roleOps maps ++
  [.publicWord 4 0,.binary .add 4 4 1,.read 5 4,.binary .mul 6 10 5,.publicWord 17 1,
   .binary .add 6 17 6,.binary .add 6 6 14,.read 7 6,.publicWord 18 3,.binary .add 18 18 0,
   .write 18 7,.constant 19 1,.binary .add 0 0 19]

/-- Register the resident owner scan as a scheduler pass that returns its advanced occurrence
cursor. -/
def worker (maps : Bool) : Schedule.Pass := ⟨_,_,_,template (code maps) 0⟩

/-- Schedule the owner scan from zero to the occurrence count with pointers to absolute CD
identifiers, role records and the owner output, plus the selected layout. -/
def visit (maps : Bool) (count absoluteCD roleBase layout ownerBase : Expr) : Visit :=
  ⟨worker maps,.lit 0,count,![absoluteCD,roleBase,layout,ownerBase]⟩

/-- Compute the role-word offset within a four-word old-arc record from the selected layout and
the local field or party-map tag. -/
def offset (maps : Bool) (layout tag : Word w) : Word w :=
  let lo := BinaryOp.mod.eval tag 2
  let mid := BinaryOp.mod.eval (BinaryOp.div.eval tag 2) 2
  let hi := BinaryOp.div.eval tag four
  if maps then mux hi (mux mid lo (mux lo layout 2)) (mux lo (2*layout) (2-layout))
    else mux (lo*mid) layout 2

private theorem div_cast {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    BinaryOp.div.eval (x : Word w) (y : Word w) = ((x/y : ℕ) : Word w) := by
  change Fin.ofNat _ ((x % 2^w)/(y % 2^w)) = _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rfl

private theorem remainder_cast {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    BinaryOp.mod.eval (x : Word w) (y : Word w) = ((x%y : ℕ) : Word w) := by
  change Fin.ofNat _ ((x % 2^w)%(y % 2^w)) = _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rfl

private theorem offset_nat (maps : Bool) (layout : Word w) (t : ℕ) (hw : 6 < 2^w) (ht : t < 6) :
    offset maps layout (t : Word w) =
      if maps then mux ((t/4 : ℕ) : Word w)
        (mux ((t/2%2 : ℕ) : Word w) ((t%2 : ℕ) : Word w) (mux ((t%2 : ℕ) : Word w) layout 2))
        (mux ((t%2 : ℕ) : Word w) (2*layout) (2-layout))
      else mux (((t%2 : ℕ) : Word w)*((t/2%2 : ℕ) : Word w)) layout 2 := by
  unfold offset
  rw [four_eq]
  have h₂ : 2 < 2^w := by omega
  have h₄ : 4 < 2^w := by omega
  have h := ht.trans hw
  have hd : t/2 < 2^w := (Nat.div_le_self ..).trans_lt h
  have r₂ := remainder_cast h h₂
  have d₂ := div_cast h h₂
  have dr := remainder_cast hd h₂
  have d₄ := div_cast h h₄
  simp only [Nat.cast_ofNat] at r₂ d₂ dr d₄
  rw [r₂,d₂,dr,d₄]

/-- Bit decoding agrees with the party-role table in both layouts. -/
theorem offset_party (layout : Bool) (t : Fin 6) (hw : 6 < 2^w) :
    offset true (layout.toNat : Word w) (t.val : Word w) = (SlotOwners.roleOffset (partyRole layout t) : Word w) := by
  rw [offset_nat true _ _ hw t.isLt]
  cases layout <;> fin_cases t <;> simp [mux, partyRole, SlotOwners.roleOffset]; ring

/-- Bit decoding agrees with the owner of each absorbed edge type. -/
theorem offset_hidden (layout : Bool) (t : Fin 4) (hw : 6 < 2^w) :
    offset false (layout.toNat : Word w) (t.val : Word w) = (SlotOwners.roleOffset (internalRole layout t) : Word w) := by
  rw [offset_nat false _ _ hw (t.isLt.trans (by decide))]
  cases layout <;> fin_cases t <;> simp [mux, internalRole, partyRole, supply, supplySource, SlotOwners.roleOffset]

/-- Address of the occurrence's absolute CD identifier, using the quotient of its cursor by the
number of occurrences per motif. -/
def absoluteAddr (maps : Bool) (p : Fin 4 → Word w) (s : Word w) :=
  p 0 + BinaryOp.div.eval s (radix maps)

/-- Address of the packed-owner word in the old arc's four-word role record, using the stored
CD identifier and the occurrence's selected role. -/
def roleAddr (maps : Bool) (p : Fin 4 → Word w) (m : Memory w) (s : Word w) :=
  p 1 + four*m (absoluteAddr maps p s).val + offset maps (p 2) (BinaryOp.mod.eval s (radix maps))

theorem absoluteAddr_eq (maps : Bool) (p : Fin 4 → Word w) (s : Word w) :
    absoluteAddr maps p s = p 0 + BinaryOp.div.eval s (arity maps : Word w) := by
  rw [absoluteAddr,radix_eq]

theorem roleAddr_eq (maps : Bool) (p : Fin 4 → Word w) (m : Memory w) (s : Word w) :
    roleAddr maps p m s = p 1 + 4*m (absoluteAddr maps p s).val +
      offset maps (p 2) (BinaryOp.mod.eval s (arity maps : Word w)) := by rw [roleAddr,four_eq,radix_eq]

/-- Trace of one owner visit, reading the motif identifier and selected role word, writing that
owner at the occurrence cursor, and returning the next cursor. -/
def report (maps : Bool) (p : Fin 4 → Word w) (s : Word w) (m : Memory w) : Report w :=
  let abs := absoluteAddr maps p s
  let role := roleAddr maps p m s
  let value := m role.val
  ⟨List.replicate (14+(roleOps maps).length) .tick ++ [.read abs (m abs.val)] ++
    List.replicate 4 .tick ++ [.read role value] ++ List.replicate 2 .tick ++
    [.write (p 3+s) value] ++ List.replicate 2 .tick, some (s+1)⟩

theorem length_code (maps : Bool) : (code maps).length = if maps then 39 else 29 := by cases maps <;> rfl

theorem native (maps : Bool) (p : Fin 4 → Word w) (s : Word w) (m : Memory w) :
    let M := (worker maps).table.instantiate w p
    execute M.program (1+(code maps).length) (M.program.start s) m [] = some (report maps p s m) ∧
      after m (report maps p s m).events = writeMemory m (p 3+s) (m (roleAddr maps p m s).val) ∧
      countProbes (report maps p s m).events = 3 ∧ (report maps p s m).events.length = (code maps).length ∧
      choiceBits (report maps p s m).events = [] := by
  intro M
  refine ⟨?_,?_,?_,?_,?_⟩
  · change execute ((template (code maps) 0).instantiate w p).program (1+(code maps).length)
      ⟨((template (code maps) 0).instantiate w p).entry,s,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
    rw [execute_template,run_eq_trace]
    cases maps <;> rfl
  all_goals cases maps <;> rfl

end CompressorRecords.ResidentOwners

end VPVNP
end Computability
end OAI
