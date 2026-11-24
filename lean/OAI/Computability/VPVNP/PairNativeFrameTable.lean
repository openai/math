import OAI.Computability.VPVNP.PrimedInputRAMFlow
import OAI.Computability.VPVNP.PairNativeFrameReads

/-! # Relocatable instruction rows for installing the terminal geometry frame

The arithmetic and its six external reads enter a chain of thirteen private
stores. The last two instructions hand the histogram base to the caller and
the cache base to the leaf's operand initializer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM

variable {r p : ℕ}

/-- Local source register for frame field `i`, with the twelve words occupying consecutive
registers 3 through 14. -/
def fieldReg (i : Fin 12) : Fin 24 := (i.natAdd 3).castLE (by decide)

namespace Table

variable (a : Flow r 11)
/-- Number of instruction rows for a frame prelude and its 29-row installation tail. -/
def size := a.length+29

/-- Program counter in the installation table corresponding to a label of the frame prelude. -/
def label (j : a.Label) : Fin (size a) := ⟨(a.labels j).val,by have := (a.labels j).isLt; unfold size; omega⟩

/-- Offset zero stores the frame pointer. Offsets 1 through 24 write the
twelve fields and advance the cursor. -/
def tail (j : Fin 29) : Fin (size a) := ⟨a.length+j.val,by have := j.isLt; unfold size; omega⟩
/-- Address of the next field-store row, with index twelve denoting the histogram-pointer
handoff after all fields have been written. -/
def store (i : Fin 13) : Fin (size a) := tail a ⟨1+2*i.val,by have := i.isLt; omega⟩
/-- Address of the unit cursor advance following frame field `i`, which transfers control to
the next store position. -/
def advance (i : Fin 12) : Fin (size a) := tail a ⟨2+2*i.val,by have := i.isLt; omega⟩

/-- The caller supplies the continuation instruction at `tail 27`; the
rejecting flow exit is at `tail 28`. -/
def row (reg : Fin 24 ↪ Fin r) (savedHist cacheDst : Fin r) (emb : Fin (size a) → Fin p)
    (finish : Instr 2 p r 11) (pc : Fin (size a)) : Instr 2 p r 11 :=
  if h : pc.val < a.length then
    ((a.code (a.labels.symm ⟨pc.val,h⟩)).map (fun t => (t.map (emb ∘ label a)).getD (emb (tail a 0)))).emit
      (emb (tail a 28))
  else
    let j := pc.val - a.length
    if j = 0 then .storePrivate (reg 9) (reg 2) (emb (store a 0))
    else if h : (j-1)/2 < 12 then
      let i : Fin 12 := ⟨(j-1)/2,h⟩
      if (j-1)%2 = 0 then .storePrivate (reg 18) (reg (fieldReg i)) (emb (advance a i))
      else .binary .add (reg 18) (reg 18) (reg 15) (emb (store a i.succ))
    else if j = 25 then .copy savedHist (reg 14) (emb (tail a 26))
    else if j = 26 then .copy cacheDst (reg 11) (emb (tail a 27))
    else if j = 27 then finish else .reject

variable (reg : Fin 24 ↪ Fin r) (savedHist cacheDst : Fin r) (emb : Fin (size a) → Fin p)
  (finish : Instr 2 p r 11)

theorem at_label (j : a.Label) :
    row a reg savedHist cacheDst emb finish (label a j) =
      ((a.code j).map (fun t => (t.map (emb ∘ label a)).getD (emb (tail a 0)))).emit (emb (tail a 28)) := by
  simp [row,label,(a.labels j).isLt]

theorem at_pointer : row a reg savedHist cacheDst emb finish (tail a 0) =
    .storePrivate (reg 9) (reg 2) (emb (store a 0)) := by simp [row,tail]

theorem at_store (i : Fin 12) : row a reg savedHist cacheDst emb finish (store a i.castSucc) =
    .storePrivate (reg 18) (reg (fieldReg i)) (emb (advance a i)) := by
  have hi : i.val < 12 := i.isLt
  simp [row,store,tail,hi]

theorem at_advance (i : Fin 12) : row a reg savedHist cacheDst emb finish (advance a i) =
    .binary .add (reg 18) (reg 18) (reg 15) (emb (store a i.succ)) := by
  have hi : i.val < 12 := i.isLt
  have sub : 2+2*i.val-1 = 2*i.val+1 := by omega
  have div : (2*i.val+1)/2 = i.val := by omega
  simp [row,advance,tail,hi,sub,div]

theorem at_hist : row a reg savedHist cacheDst emb finish (store a (Fin.last 12)) =
    .copy savedHist (reg 14) (emb (tail a 26)) := by simp [row,store,tail]

theorem at_cache : row a reg savedHist cacheDst emb finish (tail a 26) =
    .copy cacheDst (reg 11) (emb (tail a 27)) := by simp [row,tail]

theorem at_done : row a reg savedHist cacheDst emb finish (tail a 27) = finish := by simp [row,tail]
theorem at_bad : row a reg savedHist cacheDst emb finish (tail a 28) = .reject := by simp [row,tail]

theorem linked {w : ℕ} (M : Machine w p r 11)
    (rows : ∀ j, M.code (emb j) = (row a reg savedHist cacheDst emb finish j).resize w) :
    Flow.Linked M a (emb ∘ label a) (emb (tail a 0)) (emb (tail a 28)) := by
  constructor
  intro j; rw [Function.comp_apply,rows,at_label]

end Table
end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
