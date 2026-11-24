import OAI.Computability.VPVNP.PairSimulationLeafCacheWrite
import OAI.Computability.VPVNP.PrimedInputRAMFlow

/-!
# A native arithmetic prelude followed by the pair's private cache stores

The first addresses are the labels of the arithmetic flow. Its normal exit
enters a chain of 38 private stores, each followed by one cursor increment.
The standalone table accepts at the end. The same row emitter allows a
larger scheduler to place these labels and supply the final continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeCacheTable

open BurstRAM PrivateRAM PrimedInputRAM LeafSourceLoad
variable {R p w : ℕ}

/-- Number of private stores needed for the four fixed leaf parameters and 34 auxiliary
operands. -/
abbrev count := (slots 34).length
/-- Instruction count for the arithmetic flow, two rows per cache word, and the continuation
and rejection rows. -/
def size (a : Flow R 11) := a.length + 2*count + 2

/-- Address of a label from the arithmetic flow in the prefix of the cache instruction table. -/
def label (a : Flow R 11) (l : a.Label) : Fin (size a) :=
  ⟨(a.labels l).val,by have := (a.labels l).isLt; unfold size; omega⟩

/-- The last even address is the final continuation. -/
def pc (a : Flow R 11) (i : Fin (count+1)) : Fin (size a) :=
  ⟨a.length + 2*i.val,by have := i.isLt; unfold size; omega⟩

/-- Address of the cursor increment immediately following the private store for cache slot `i`. -/
def inc (a : Flow R 11) (i : Fin count) : Fin (size a) :=
  ⟨a.length + (2*i.val+1),by have := i.isLt; unfold size; omega⟩

/-- Address reached after incrementing past the last cache word, where the enclosing program
supplies its continuation. -/
def done (a : Flow R 11) := pc a (Fin.last count)
/-- Rejecting row targeted by a failed branch of the cache arithmetic. -/
def bad (a : Flow R 11) : Fin (size a) := ⟨a.length+2*count+1,by unfold size; omega⟩

/-- Emit one row with targets in an ambient scheduler's program-counter type. -/
def row (a : Flow R 11) (src : Static 34 → Fin R) (cursor unit : Fin R)
    (embed : Fin (size a) → Fin p) (finish : Instr 2 p R 11) (i : Fin (size a)) : Instr 2 p R 11 :=
  if h : i.val < a.length then
    ((a.code (a.labels.symm ⟨i.val,h⟩)).map (fun t => (t.map (embed ∘ label a)).getD (embed (pc a 0)))).emit
      (embed (bad a))
  else
    let j := i.val - a.length
    if h : j/2 < count then
      let slot : Fin count := ⟨j/2,h⟩
      if j%2 = 0 then storeInstr src cursor (embed (inc a slot)) (slots 34)[slot]
      else incInstr cursor unit (embed (pc a slot.succ))
    else if j = 2*count then finish else .reject

variable (a : Flow R 11) (src : Static 34 → Fin R) (cursor unit : Fin R)

theorem row_flow (embed : Fin (size a) → Fin p) (finish : Instr 2 p R 11) (i : a.Label) :
    row a src cursor unit embed finish (label a i) =
      ((a.code i).map (fun t => (t.map (embed ∘ label a)).getD (embed (pc a 0)))).emit (embed (bad a)) := by
  simp [row,label,(a.labels i).isLt]

theorem row_store (embed : Fin (size a) → Fin p) (finish : Instr 2 p R 11) (i : Fin count) :
    row a src cursor unit embed finish (pc a i.castSucc) = storeInstr src cursor (embed (inc a i)) (slots 34)[i] := by
  have hi : i.val < 38 := i.isLt
  simp [row,pc,hi]

theorem row_advance (embed : Fin (size a) → Fin p) (finish : Instr 2 p R 11) (i : Fin count) :
    row a src cursor unit embed finish (inc a i) = incInstr cursor unit (embed (pc a i.succ)) := by
  have hi : i.val < 38 := i.isLt
  have half : (2*i.val+1)/2 = i.val := by omega
  simp [row,inc,half,hi]

theorem row_done (embed : Fin (size a) → Fin p) (finish : Instr 2 p R 11) :
    row a src cursor unit embed finish (done a) = finish := by simp [row,done,pc]

theorem row_bad (embed : Fin (size a) → Fin p) (finish : Instr 2 p R 11) :
    row a src cursor unit embed finish (bad a) = .reject := by
  simp [row,bad,Nat.add_assoc]

/-- Assemble a two-bit-literal program with the supplied arithmetic entry, 38
store-and-increment pairs, and an accepting continuation. -/
def template : Template (size a) R 11 where
  literalWidth := 2
  entry := label a a.entry
  code := row a src cursor unit id .accept

/-- Installing these rows anywhere in a machine links the arithmetic flow
to the first cache store. -/
theorem linked_of_rows (M : Machine w p R 11) (embed : Fin (size a) → Fin p) (finish : Instr 2 p R 11)
    (h : ∀ i, M.code (embed i) = (row a src cursor unit embed finish i).resize w) :
    Flow.Linked M a (embed ∘ label a) (embed (pc a 0)) (embed (bad a)) := by
  constructor
  intro i
  rw [Function.comp_apply,h,row_flow]

variable (pub : Fin 11 → Word w)

theorem linked :
    Flow.Linked ((template a src cursor unit).instantiate w pub) a (label a) (pc a 0) (bad a) :=
  linked_of_rows a src cursor unit _ id .accept (fun _ => rfl)

theorem store_row (i : Fin count) :
    ((template a src cursor unit).instantiate w pub).code (pc a i.castSucc) =
      storeInstr src cursor (inc a i) (slots 34)[i] := by
  change (row a src cursor unit id .accept (pc a i.castSucc)).resize w = _
  rw [row_store]; rfl

theorem advance_row (i : Fin count) :
    ((template a src cursor unit).instantiate w pub).code (inc a i) = incInstr cursor unit (pc a i.succ) := by
  change (row a src cursor unit id .accept (inc a i)).resize w = _
  rw [row_advance]; rfl

theorem done_row :
    ((template a src cursor unit).instantiate w pub).code (done a) = .accept := by
  change (row a src cursor unit id .accept (done a)).resize w = _
  rw [row_done]; rfl

theorem bad_row :
    ((template a src cursor unit).instantiate w pub).code (bad a) = .reject := by
  change (row a src cursor unit id .accept (bad a)).resize w = _
  rw [row_bad]; rfl

end PairSimulation.NativeCacheTable

end VPVNP
end Computability
end OAI
