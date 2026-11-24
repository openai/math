import OAI.Computability.VPVNP.PairNodeChildLoop

/-!
# Native loop control for absorbed shrinking fields

The public row count and ordered ID array are read from external memory.
Each ID selects one fixed-stride private slot; only the term's actual bit
width is guessed and written. Registers 0–4 are the private field mover.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM PrivateRAM NodeArguments
open scoped Fin.CommRing

variable {W p r k : ℕ}

/-- Instruction labels for initializing the owner's scan, testing its remaining count,
addressing the current private slot, and advancing to the next dense ID. -/
inductive Control where
  | one | zero | countAddr | readCount | rowOffset | rowStart | test
  | slotOffset | slotStart | slotEnd | decrement | advance
  deriving DecidableEq

instance : Fintype Control := derive_fintype% _

/-- The term width reader's input pointer, term parameters, and outputs.
Its register six retains the actual dense hidden ID on completion. -/
def widthRegs (reg : Fin 22 ↪ Fin r) : Fin 10 ↪ Fin r :=
  (⟨![5,6,7,8,9,1,10,11,12,13], by decide⟩ : Fin 10 ↪ Fin 22).trans reg

/-- Embed the five registers of the private bit-guessing loop as registers 0 through 4 of the
absorbed-field scan. -/
def guessRegs (reg : Fin 22 ↪ Fin r) : Fin 5 ↪ Fin r := (Fin.castAddEmb 17).trans reg

/-- Emit the scan instruction at a control label, with supplied entry addresses for reading the
width, guessing the bits, and leaving the scan. -/
def control (pc : Control → Fin p) (reg : Fin 22 ↪ Fin r) (width guess done : Fin p) :
    Control → Instr W p r k
  | .one => .constant (reg 3) 1 (pc .zero)
  | .zero => .constant (reg 21) 0 (pc .countAddr)
  | .countAddr => .binary .add (reg 14) (reg 17) (reg 18) (pc .readCount)
  | .readCount => .readExternal (reg 14) (reg 14) (pc .rowOffset)
  | .rowOffset => .binary .mul (reg 5) (reg 18) (reg 20) (pc .rowStart)
  | .rowStart => .binary .add (reg 5) (reg 19) (reg 5) (pc .test)
  | .test => .jumpEq (reg 14) (reg 21) done width
  | .slotOffset => .binary .mul (reg 2) (reg 10) (reg 16) (pc .slotStart)
  | .slotStart => .binary .add (reg 2) (reg 15) (reg 2) (pc .slotEnd)
  | .slotEnd => .binary .add (reg 1) (reg 2) (reg 1) guess
  | .decrement => .binary .sub (reg 14) (reg 14) (reg 3) (pc .advance)
  | .advance => .binary .add (reg 5) (reg 5) (reg 3) (pc .test)

theorem resize_control (pc : Control → Fin p) (reg : Fin 22 ↪ Fin r) (width guess done : Fin p) (j : Control) :
    (control (W := 1) (k := k) pc reg width guess done j).resize W = control pc reg width guess done j := by
  cases j <;> rfl

/-- The machine contains each scan control instruction at its assigned program counter with the
given registers and jump targets. -/
def ControlLinked (M : Machine W p r k) (pc : Control → Fin p) (reg : Fin 22 ↪ Fin r) (width guess done : Fin p) :=
  ∀ j, M.code (pc j) = control pc reg width guess done j

/-- Addresses and layout choices for one packed owner. The caller can
place the private slots at any base separated from its other scratch. -/
structure Args (W : ℕ) where
  /-- External word address of the first selected motif term record. -/
  termBase : Word W
  /-- Distance in external words between the starts of consecutive motif term records. -/
  termStride : Word W
  /-- The surviving layout of the selected terms. The width reader uses the opposite layout for
  absorbed fields. -/
  layout : Bool
  /-- Number of selector bits contributed to a hidden field by each repetition of its term. -/
  selectorBits : Word W
  /-- First private word address in the array of slots for guessed hidden fields. -/
  scratchBase : ℕ
  /-- Distance in private words between slots for consecutive dense hidden-field IDs. -/
  slotStride : ℕ
  /-- External base address of the table giving the number of hidden fields for each packed
  owner. -/
  countBase : ℕ
  /-- Ordinal of the packed site whose count and ordered row of hidden-field IDs the scan
  reads. -/
  owner : ℕ
  /-- External address where the array of owners' ordered hidden-field ID rows begins. -/
  rowBase : ℕ
  /-- Distance in external words from one packed owner's ID row to the next. -/
  rowStride : ℕ

/-- Start address of this owner's external ID row, computed as the row base plus the owner
ordinal times the row stride. -/
def Args.row (g : Args W) := g.rowBase + g.owner*g.rowStride

/-- Start address of the private bit slot for a dense hidden-field ID, computed as the scratch
base plus the ID times the slot stride. -/
def Args.slot (g : Args W) (id : ℕ) := g.scratchBase + id*g.slotStride

/-- The ten designated input registers hold the term parameters, private slot geometry, owner
ordinal, and external count and row addresses required by the scan. -/
structure Inputs (g : Args W) (reg : Fin 22 ↪ Fin r) (c : Config W p r) : Prop where
  term : c.reg (reg 6) = g.termBase
  termStride : c.reg (reg 7) = g.termStride
  layout : c.reg (reg 8) = (g.layout.toNat : Word W)
  selectors : c.reg (reg 9) = g.selectorBits
  scratch : c.reg (reg 15) = (g.scratchBase : Word W)
  stride : c.reg (reg 16) = (g.slotStride : Word W)
  counts : c.reg (reg 17) = (g.countBase : Word W)
  owner : c.reg (reg 18) = (g.owner : Word W)
  rows : c.reg (reg 19) = (g.rowBase : Word W)
  rowStride : c.reg (reg 20) = (g.rowStride : Word W)

/-- The scan inputs are loaded, and registers 3 and 21 hold the constants one and zero for the
loop counter and guard. -/
structure Ready (g : Args W) (reg : Fin 22 ↪ Fin r) (c : Config W p r) : Prop extends Inputs g reg c where
  one : c.reg (reg 3) = 1
  zero : c.reg (reg 21) = 0

/-- All modifications after the initial constant rows. -/
def scratch : List (Fin 22) := [0,1,2,4,5,10,11,12,13,14]

/-- The two configurations agree on every register outside the scan's embedded scratch
registers. -/
def Frame (reg : Fin 22 ↪ Fin r) (c d : Config W p r) :=
  ∀ i, (∀ j ∈ scratch, i ≠ reg j) → d.reg i = c.reg i

theorem Frame.trans {reg : Fin 22 ↪ Fin r} {a b c : Config W p r} (h : Frame reg a b) (h' : Frame reg b c) :
    Frame reg a c := fun i hi => (h' i hi).trans (h i hi)

theorem Frame.atReg {reg : Fin 22 ↪ Fin r} {c d : Config W p r} (h : Frame reg c d)
    (j : Fin 22) (hj : j ∉ scratch) : d.reg (reg j) = c.reg (reg j) :=
  h _ (fun _ ht => reg.injective.ne (fun eq => hj (eq ▸ ht)))

theorem Ready.frame {reg : Fin 22 ↪ Fin r} {g : Args W} {c d : Config W p r}
    (ready : Ready g reg c) (h : Frame reg c d) : Ready g reg d :=
  ⟨⟨(h.atReg _ (by decide)).trans ready.term, (h.atReg _ (by decide)).trans ready.termStride,
    (h.atReg _ (by decide)).trans ready.layout, (h.atReg _ (by decide)).trans ready.selectors,
    (h.atReg _ (by decide)).trans ready.scratch, (h.atReg _ (by decide)).trans ready.stride,
    (h.atReg _ (by decide)).trans ready.counts, (h.atReg _ (by decide)).trans ready.owner,
    (h.atReg _ (by decide)).trans ready.rows, (h.atReg _ (by decide)).trans ready.rowStride⟩,
    (h.atReg _ (by decide)).trans ready.one, (h.atReg _ (by decide)).trans ready.zero⟩

theorem frame_put {reg : Fin 22 ↪ Fin r} (c : Config W p r) (next : Fin p) (j : Fin 22)
    (v : Word W) (hj : j ∈ scratch) : Frame reg c (c.put next (reg j) v) :=
  fun _ hi => Function.update_of_ne (hi j hj) _ _

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
