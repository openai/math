import OAI.Computability.VPVNP.PairNativeOperandVector
import OAI.Computability.VPVNP.PairNativeCacheTable
import OAI.Computability.VPVNP.PairSimulationLeafCachedSources
import OAI.Computability.VPVNP.PairSimulationLeafSourceOperands

/-! # The private operand-cache program embedded in a final-vertex pair burst

The native arithmetic reads only the eleven public operands and the runtime
cache-base word. The store tail writes each result at its designated offset.
All labels and registers can be relocated in the surrounding vertex table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeCache
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM LiveProgram NativeOperands LeafSourceLoad
open scoped Fin.CommRing

/-- Expression for the cache word at index `i`, in the order of the four virtual-machine
parameters followed by the 34 auxiliary public operands. -/
abbrev args (c : Constants) (i : Fin 38) : InputOperand := expr c ((slots 34)[i.val]'i.isLt)
/-- Number of native registers allocated to evaluate all 38 expressions and retain their
results for the cache stores. -/
abbrev bankSize (c : Constants) := NativeOperands.registerCount (capacity (args c))

/-- Index of a fixed leaf source in the cache vector, given by its offset from the private
cache base. -/
def number (j : Static 34) : Fin 38 := ⟨j.offset, by cases j <;> simp [Static.offset]; omega⟩
/-- Register holding the evaluated word for leaf source `j` when the native arithmetic prelude
finishes. -/
def resultReg (c : Constants) (j : Static 34) : Fin (bankSize c) := src (args c) (number j)

theorem args_number (c : Constants) (j : Static 34) : args c (number j) = expr c j := by
  obtain ⟨i,hi,h⟩ := List.mem_iff_getElem.mp (mem_slots j)
  have hn : j.offset = i := h ▸ slot_offset (k := 34) ⟨i,hi⟩
  unfold args number
  simp only [hn,h]

/-- Native operand-vector program that derives the pair geometry and evaluates the 38 cache
expressions using bucket parameters `a` and `b`. -/
abbrev block (c : Constants) (a b : ℕ) := vector (args c) a b

/-- Place the cache arithmetic in the caller's register bank through `reg`, keeping its eleven
public operand indices. -/
abbrev relocated {R : ℕ} (c : Constants) (a b : ℕ) (reg : Fin (bankSize c) ↪ Fin R) :=
  PrimedCounter.renameFlow reg id (block c a b)

/-- Standalone initializer that runs the pair's 38 operand expressions in their native bank,
stores them at successive private addresses, and accepts. -/
def template (c : Constants) (a b : ℕ) :=
  NativeCacheTable.template (relocated c a b (Function.Embedding.refl _))
    (resultReg c) (cursor (args c)) (unit (args c))

theorem template_rows (c : Constants) (a b w : ℕ) (pub : Fin 11 → Word w) (i) :
    ((template c a b).instantiate w pub).code i =
      (NativeCacheTable.row (relocated c a b (Function.Embedding.refl _)) (resultReg c)
        (cursor (args c)) (unit (args c)) id .accept i).resize w := rfl

theorem work_le (c : Constants) (a b : ℕ) (g : Geometry) :
    work (args c) a b g + 76 ≤ 4*a*(g.n.log2+1) + (a+b+109) +
      38*(Finset.univ.sup (fun i => fieldCost 0 (args c i)) * (g.w+1)) := by
  have h := PairNativeGeometry.ticks_le a b g.n
  change PairNativeGeometry.ticks a b g.n + 38*((Finset.univ.sup fun i => fieldCost 0 (args c i))*(g.w+1)) + 3 + 76 ≤ _
  omega

/-- Arithmetic prepares every store source in its actual native register,
leaving registers outside the chosen embedding available to the caller. -/
theorem prelude {R : ℕ} (c : Constants) (g : Geometry) (lit : LiteralPrefix)
    (a b : ℕ) (reg : Fin (bankSize c) ↪ Fin R)
    (hb : 0 < b) (hn : 0 < g.n) (hwidth : g.w = (g.d+10)^4) (hbucket : g.H = 2^roundedUp a b g.n)
    (fit : PairNativeGeometry.Fits a b g.n g.w) (hf : ∀ j, FieldFits g (expr c j))
    (pub : Fin 11 → Word g.w) (h6 : (pub 6).val = g.n) (h7 : (pub 7).val = g.d)
    (h1 : pub 1 = Fin.ofNat _ lit.length) (h0 : pub 0 = Fin.ofNat _ lit.value)
    (st : Word g.w) (m : Memory g.w) (rs : Regs g.w R) :
    ∃ t ≤ work (args c) a b g, ∃ out,
      Flow.Exec pub st (relocated c a b reg) rs m (List.replicate t .tick) out m ∧
      (∀ j : Static 34, out (reg (resultReg c j)) = Pieces.word g lit (expr c j)) ∧
      out (reg (cursor (args c))) = rs (reg (saved (args c))) ∧ out (reg (unit (args c))) = 1 ∧
      ∀ j, j ∉ Set.range reg → out j = rs j := by
  obtain ⟨t,ht,small,run,done⟩ := vector_run (args c) g lit a b hb hn hwidth hbucket fit
    (fun i => hf _) pub h6 h7 h1 h0 st m (rs ∘ reg)
  obtain ⟨out,large,restrict,other⟩ := PrimedCounter.liftExec reg id pub run rs rfl
  refine ⟨t,ht,out,large,?_,(congrFun restrict _).trans done.pointer,(congrFun restrict _).trans done.one,other⟩
  intro j
  exact (congrFun restrict _).trans ((done.value (number j)).trans (congrArg (Pieces.word g lit) (args_number c j)))

end PairSimulation.NativeCache

end VPVNP
end Computability
end OAI
