import OAI.Computability.VPVNP.PairShrinkHiddenGuess
import OAI.Computability.VPVNP.CompressorRegisterSetupTrace

/-!
# Loading the published addresses used by the absorbed-field scan

The live old-level header contains the owner-count and ordered-row heads, the
term array's base and stride, and the selected layout. Stage constants use
the native binary literal compiler. The owner and private slot geometry come
from the enclosing node visit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess.Header

open BurstRAM PrivateRAM CompressorRecords PhaseRecipe NodeArguments.ChildScan
open scoped Fin.CommRing

/-- The ten expressions that initialize the scan from five old-level header cells, the owner's
three live operands, and the selector-width and row-stride literals. -/
def recipe (selectorBits rowStride : ℕ) : Fin 10 → Expr :=
  ![.header 36, .header 37, .header 38, .lit selectorBits, .publicWord 1, .publicWord 2,
    .header 31, .publicWord 0, .header 32, .lit rowStride]

/-- Map each of the ten header recipe outputs to its destination in the scan's 22-register
bank. -/
def target : Fin 10 → Fin 22 := ![6,7,8,9,15,16,17,18,19,20]

variable {W p r k : ℕ}

/-- Absolute old-level header cells in the completed external directory. -/
structure Published (g : Args W) (oldLevel : ℕ) (m : Memory W) : Prop where
  counts : m (oldLevel+31) = (g.countBase : Word W)
  rows : m (oldLevel+32) = (g.rowBase : Word W)
  term : m (oldLevel+36) = g.termBase
  stride : m (oldLevel+37) = g.termStride
  layout : m (oldLevel+38) = (g.layout.toNat : Word W)

/-- The chronological instruction trace of the header compiler. -/
def trace (selectors rowStride : ℕ) (inputs : Fin 6 → Fin r)
    (vm : Fin (RegisterSetup.regCount (recipe selectors rowStride)) ↪ Fin r)
    (c : Config W p r) (m : Memory W) : List (Event W) :=
  (RowRecipe.evaluate (fun i : Fin 5 => c.reg (inputs i.castSucc)) (c.reg (inputs (Fin.last 5)))
    m (RegisterSetup.lines (recipe selectors rowStride)) (fun i => c.reg (vm i))).1

/-- Each of the five external values is read once. No guesses are consumed
and the private memory remains available to the actual hidden loop. -/
theorem raw_run (M : Machine W p r k) (g : Args W) (m : Memory W) (oldLevel : ℕ)
    (selectors rowStride : ℕ) (sel : g.selectorBits = (selectors : Word W)) (stride : g.rowStride = rowStride)
    (inputs : Fin 6 → Fin r) (pc : ℕ → Fin p) (reg : Fin 22 ↪ Fin r)
    (vm : Fin (RegisterSetup.regCount (recipe selectors rowStride)) ↪ Fin r)
    (link : RegisterSetup.Linked vm inputs M pc (RegisterSetup.lines (recipe selectors rowStride)))
    (safe : ∀ i j, vm i ≠ inputs j)
    (outputs : ∀ i, vm (RegisterSetup.output (recipe selectors rowStride) i) = reg (target i))
    (c : Config W p r) (atStart : c.pc = pc 0) (hL : c.reg (inputs 5) = (oldLevel : Word W))
    (ho : c.reg (inputs 0) = (g.owner : Word W)) (hs : c.reg (inputs 1) = (g.scratchBase : Word W))
    (hz : c.reg (inputs 2) = (g.slotStride : Word W))
    (fits : oldLevel+38 < 2^W) (headers : Published g oldLevel m) :
    let es := trace selectors rowStride inputs vm c m
    ∃ d, Prefix M m c d [] es ∧ es.length = (RegisterSetup.lines (recipe selectors rowStride)).length ∧
      countProbes es = 5 ∧ choiceBits es = [] ∧ d.pc = pc (RegisterSetup.lines (recipe selectors rowStride)).length ∧
      Inputs g reg d ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j := by
  obtain ⟨d,len,probes,choices,ep,priv,pers,vals,frame,pref⟩ :=
    RegisterSetup.execute_setup_raw (recipe selectors rowStride) inputs vm M m pc link safe c atStart
  let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
  have eqAt (i : Fin 10) : d.reg (reg (target i)) = (recipe selectors rowStride i).eval pub
      (c.reg (inputs (Fin.last 5))) m := (outputs i) ▸ vals i
  have head (j : ℕ) (hj : j ≤ 38) :
      (Expr.header j).eval pub (c.reg (inputs (Fin.last 5))) m = m (oldLevel+j) := by
    change m ((c.reg (inputs 5))+(j : Word W)).val = _
    rw [hL, ← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have loadCount : ∑ i, (recipe selectors rowStride i).loads = 5 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, recipe, Expr.header, Expr.headerAddress, Expr.add]
    rfl
  refine ⟨d,pref,len,probes.trans loadCount,choices,ep,?_,priv,pers,frame⟩
  exact ⟨(eqAt 0).trans ((head 36 (by decide)).trans headers.term),
    (eqAt 1).trans ((head 37 (by decide)).trans headers.stride),
    (eqAt 2).trans ((head 38 (by decide)).trans headers.layout), (eqAt 3).trans sel.symm,
    (eqAt 4).trans hs, (eqAt 5).trans hz, (eqAt 6).trans ((head 31 (by decide)).trans headers.counts),
    (eqAt 7).trans ho, (eqAt 8).trans ((head 32 (by decide)).trans headers.rows),
    (eqAt 9).trans (congrArg (fun n : ℕ => (n : Word W)) stride.symm)⟩

/-- Each of the five external values is read once. No guesses are consumed
and the private memory remains available to the actual hidden loop. -/
theorem run (M : Machine W p r k) (g : Args W) (m : Memory W) (oldLevel : ℕ)
    (selectors rowStride : ℕ) (sel : g.selectorBits = (selectors : Word W)) (stride : g.rowStride = rowStride)
    (inputs : Fin 6 → Fin r) (pc : ℕ → Fin p) (reg : Fin 22 ↪ Fin r)
    (vm : Fin (RegisterSetup.regCount (recipe selectors rowStride)) ↪ Fin r)
    (link : RegisterSetup.Linked vm inputs M pc (RegisterSetup.lines (recipe selectors rowStride)))
    (safe : ∀ i j, vm i ≠ inputs j)
    (outputs : ∀ i, vm (RegisterSetup.output (recipe selectors rowStride) i) = reg (target i))
    (c : Config W p r) (atStart : c.pc = pc 0) (hL : c.reg (inputs 5) = (oldLevel : Word W))
    (ho : c.reg (inputs 0) = (g.owner : Word W)) (hs : c.reg (inputs 1) = (g.scratchBase : Word W))
    (hz : c.reg (inputs 2) = (g.slotStride : Word W))
    (fits : oldLevel+38 < 2^W) (headers : Published g oldLevel m) :
    ∃ es d, Prefix M m c d [] es ∧ es.length = (RegisterSetup.lines (recipe selectors rowStride)).length ∧
      countProbes es = 5 ∧ choiceBits es = [] ∧ d.pc = pc (RegisterSetup.lines (recipe selectors rowStride)).length ∧
      Inputs g reg d ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j := by
  obtain ⟨d,result⟩ := raw_run M g m oldLevel selectors rowStride sel stride inputs pc reg vm link safe outputs c atStart hL ho hs hz fits headers
  exact ⟨_,d,result⟩

end PairSimulation.ShrinkHiddenGuess.Header

end VPVNP
end Computability
end OAI
