import OAI.Hierarchy.ProtocolRAMCalendarSliceROM

namespace OAI
/-! # Two consecutive immutable ROMs for integral feeding and half-stock acquisition -/

namespace Hierarchy.ProtocolRAM.Calendar.FeedROM

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing
variable {w : ℕ}

def sliceBank (initial footprint steps cap width : ℕ) :=
  sliceROM (initial+footprint) steps (cap*width+1)

def halfBank (initial footprint steps cap width : ℕ) : Bank :=
  let table := sliceBank initial footprint steps cap width
  ⟨table.base+table.size,ProtocolRAMPurchaseSampler.bits (cap*width+1)⟩

def halfAdvice (bank : Bank) (m : Memory w) : Memory w :=
  fillSegment bank.base bank.size (fun a=>((a-bank.base)/2:ℕ)) m

def mount (initial footprint steps cap width : ℕ) (rest : Memory w) : Memory w :=
  halfAdvice (halfBank initial footprint steps cap width)
    (feedAdvice (sliceBank initial footprint steps cap width) steps (cap*width+1) rest)

theorem slot_fits (initial footprint steps cap width : ℕ) {value : ℕ} (bounded : value ≤ cap*width) :
    value<(halfBank initial footprint steps cap width).size :=
  bounded.trans_lt ((Nat.lt_succ_self _).trans (ProtocolRAMPurchaseSampler.lt_span _))

theorem half_read (bank : Bank) (m : Memory w) (x : Word w) (fit : x.val<bank.size) :
    (bank.read (halfAdvice bank m) x).val=x.val/2 := by
  have inside : bank.base≤bank.base+x.val ∧ bank.base+x.val<bank.base+bank.size :=
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left fit _⟩
  simp [Bank.read,halfAdvice,fillSegment,Nat.mod_eq_of_lt fit,inside,
    Fin.val_cast_of_lt ((Nat.div_le_self x.val 2).trans_lt x.isLt)]

theorem half_cell (bank : Bank) (m : Memory w) (x : ℕ) (hx : x<bank.size) :
    halfAdvice bank m (bank.base+x)=((x/2:ℕ):Word w) := by
  have inside : bank.base≤bank.base+x ∧ bank.base+x<bank.base+bank.size :=
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left hx _⟩
  simp [halfAdvice,fillSegment,inside]

theorem slice_cell (initial footprint steps cap width : ℕ) (rest : Memory w) (a : ℕ)
    (endAt : a<(sliceBank initial footprint steps cap width).base+steps*(cap*width+1)) :
    mount initial footprint steps cap width rest a=
      feedAdvice (sliceBank initial footprint steps cap width) steps (cap*width+1) rest a := by
  have enough := sliceROM_size (initial+footprint) steps (cap*width+1)
  have next : a<(halfBank initial footprint steps cap width).base := endAt.trans_le (Nat.add_le_add_left enough _)
  simp [mount,halfAdvice,fillSegment,not_le.mpr next]

theorem before_stock (initial footprint steps cap width : ℕ) (rest : Memory w) (a : ℕ) (inside : a < initial+footprint) :
    mount initial footprint steps cap width rest a=rest a := by
  have first : a<(sliceBank initial footprint steps cap width).base := inside
  rw [slice_cell]
  · simp [feedAdvice,fillSegment,not_le.mpr first]
  · exact first.trans_le (Nat.le_add_right ..)

/-- A true live ROM handle requires only its word range to survive the prefix. -/
theorem read_frame (bank : Bank) (m fixture : Memory w) (x : Word w)
    (fit : x.val<bank.size) (frame : ∀ a, bank.base≤a → a<bank.base+bank.size → m a=halfAdvice bank fixture a) :
    (bank.read m x).val=x.val/2 := by
  have r : bank.read m x=bank.read (halfAdvice bank fixture) x := by
    simp only [Bank.read,Nat.mod_eq_of_lt fit]
    exact frame _ (Nat.le_add_right ..) (Nat.add_lt_add_left fit _)
  exact (congrArg Fin.val r).trans (half_read bank fixture x fit)

theorem end_le (initial footprint steps cap width : ℕ) :
    (halfBank initial footprint steps cap width).base+(halfBank initial footprint steps cap width).size≤
      initial+footprint+2*(steps*(cap*width+1)+1)+2*(cap*width+2) := by
  have slice := sliceROM_size_le (initial+footprint) steps (cap*width+1)
  have half := ProtocolRAMPurchaseSampler.span_le (cap*width+1)
  exact Nat.add_le_add (Nat.add_le_add_left slice _) half

end Hierarchy.ProtocolRAM.Calendar.FeedROM

end OAI
