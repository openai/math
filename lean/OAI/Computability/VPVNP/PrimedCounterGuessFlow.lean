import OAI.Computability.VPVNP.PrimedCounterGuessWord
import OAI.Computability.VPVNP.PrimedInputRAMFlow

/-!
# Compiling the word-guess loop in the auxiliary program

The word chooser is a structured block in the same finite control graph as
the input passes, stack operations, mark checks, and histogram comparison.
Its native correctness holds at any linked occurrence in that graph.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.GuessWord

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM

variable {r k p w : ℕ}

/-- Structured representation of the eight instructions for one word. -/
def flow (reg : Fin 3 ↪ Fin r) : Flow r k :=
  .seq (.line (.constant (reg 2) 0)) <|
  .seq (.line (.constant (reg 0) 0)) <|
  .seq (.line (.constant (reg 1) 1)) <|
  .whileLt (reg 2) (reg 1) <| .seq
    (.branch (.line (.binary .add (reg 0) (reg 0) (reg 1)))
             (.line (.binary .add (reg 0) (reg 0) (reg 2))))
    (.line (.binary .add (reg 1) (reg 1) (reg 1)))

/-- Local labels in instruction order, from the first constant to the doubling. -/
def flowLabels (reg : Fin 3 ↪ Fin r) : Fin 8 → (flow (k := k) reg).Label :=
  ![.inl (), .inr (.inl ()), .inr (.inr (.inl ())), .inr (.inr (.inr (.inl ()))),
    .inr (.inr (.inr (.inr (.inl (.inl ()))))),
    .inr (.inr (.inr (.inr (.inl (.inr (.inl ())))))),
    .inr (.inr (.inr (.inr (.inl (.inr (.inr ())))))),
    .inr (.inr (.inr (.inr (.inr ()))))]

theorem contains_flow {M : Machine w p r k} {reg : Fin 3 ↪ Fin r}
    {label : (flow (k := k) reg).Label → Fin p} {done bad : Fin p}
    (hc : Flow.Linked M (flow reg) label done bad) :
    Contains M (label ∘ flowLabels reg) reg done := by
  intro i
  fin_cases i <;> exact hc.atLabel (flowLabels reg _)

/-- A full word read inside a compiled compound program reaches the next
linked block with its output register set to the chosen word. -/
theorem flow_native {M : Machine w p r k} {reg : Fin 3 ↪ Fin r}
    {label : (flow (k := k) reg).Label → Fin p} {done bad : Fin p}
    (hc : Flow.Linked M (flow reg) label done bad) (c : Config w p r)
    (hpc : c.pc = label (flow reg).entry) (v : Word w) :
    ∃ out es, Prefix M c es out ∧ es.length = 4*w+4 ∧ choiceBits es = wordBits v ∧
      out.pc = done ∧ out.reg (reg 0) = v ∧ (∀ j, j ∉ Set.range reg → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent :=
  native M _ reg done (contains_flow hc) c hpc v

theorem flow_native_exact {M : Machine w p r k} {reg : Fin 3 ↪ Fin r}
    {label : (flow (k := k) reg).Label → Fin p} {done bad : Fin p}
    (hc : Flow.Linked M (flow reg) label done bad) (c : Config w p r)
    (hpc : c.pc = label (flow reg).entry) (v : Word w) :
    Prefix M c (trace v) ⟨done, c.persistent, resultRegs reg c.reg v, c.privateMem⟩ :=
  native_exact M _ reg done (contains_flow hc) c hpc v

end PrimedCounter.GuessWord

end VPVNP
end Computability
end OAI
