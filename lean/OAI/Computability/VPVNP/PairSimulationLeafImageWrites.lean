import OAI.Computability.VPVNP.PairSimulationLeafImage
import OAI.Computability.VPVNP.PairSimulationRouteBankWrites
import OAI.Computability.VPVNP.PairSimulationLeafBootWrites

/-!
# Register writes of the native cursor leaf

The destination of every writing instruction belongs to the leaf's allocated
registers. An enclosing machine may keep its virtual public operands in any
disjoint bank, including during external reads and on rejected paths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafImage

open BurstRAM PrivateRAM RegisterOperands RAMTape LeafStartup

variable {w p r k : ℕ}

private theorem of_some {α : Type*} (reg : α ↪ Fin r) {j : α} {a : Fin r}
    (h : some (reg j) = some a) : a ∈ Set.range reg :=
  ⟨j, Option.some.inj h⟩

private theorem address_mem (pc : Fin 20 → Fin p) (reg : LeafAddress.Reg ↪ Fin r)
    (pub : LeafAddress.Field → Fin k) (launch transit : Fin p) (i : Fin 20) (a : Fin r)
    (h : destination (LeafAddress.instruction (w := w) pc reg pub launch transit i) = some a) :
    a ∈ Set.range reg := by
  fin_cases i <;> first | exact of_some reg h | contradiction

private theorem prepare_mem (pc : RoutePrepare.Stage → Fin p) (reg : Fin 32 ↪ Fin r)
    (leaf : LeafAddress.Reg ↪ Fin r) (pub : RoutePrepare.Field → Fin k) (done : Fin p)
    (i : RoutePrepare.Stage) (a : Fin r)
    (h : destination (RoutePrepare.instruction (W := w) pc reg leaf pub done i) = some a) :
    a ∈ Set.range reg := by
  cases i with
  | inl i | inr i => fin_cases i <;> exact of_some reg h

private theorem handoff_mem (pc : Fin 7 → Fin p) (boot : LeafBoot.Reg ↪ Fin r)
    (leaf : LeafAddress.Reg ↪ Fin r) (pub : RoutePrepare.Field → Fin k) (done : Fin p)
    (i : Fin 7) (a : Fin r)
    (h : destination (LeafBootHandoff.instruction (w := w) pc boot leaf pub done i) = some a) :
    a ∈ Set.range boot := by
  fin_cases i <;> exact of_some boot h

private theorem stack_mem {K Q : Type} (code : StackCode K Q) (pc : Q → Fin 7 → Fin p)
    (reg : StackMachine.Register K ↪ Fin r) (done : Fin p) (q : Q) (i : Fin 7) (a : Fin r)
    (h : destination (StackMachine.instruction (w := w) (k := k) code pc reg done q i) = some a) :
    a ∈ Set.range reg := by
  cases op : code q with
  | push _ _ _ | pop _ _ | goto _ | choose _ _ =>
    fin_cases i <;> simp [StackMachine.instruction, op, destination] at h <;> exact ⟨_,h⟩
  | halt b =>
    cases b <;> fin_cases i <;> simp [StackMachine.instruction, op, destination] at h
    exact ⟨_,h⟩

/-- Every register written by the composite leaf belongs to its physical register
embedding. This statement covers every opcode, independent of reachability. -/
theorem destination_mem (pc : Label → Fin p) (reg : Reg ↪ Fin r) (pub : Pub → Fin k)
    (ret : Fin p) (j : Label) (a : Fin r)
    (h : destination (instruction pc reg pub ret j) = some a) : a ∈ Set.range reg := by
  cases j with
  | address i =>
    obtain ⟨t,ht⟩ := address_mem _ (leafReg reg) _ _ _ i a h
    exact ⟨_,ht⟩
  | prepare i =>
    obtain ⟨t,ht⟩ := prepare_mem _ (routeReg reg) (leafReg reg) _ _ i a h
    exact ⟨.route t,ht⟩
  | route j =>
    cases j with
    | inl j =>
      simp only [instruction,destination_resize] at h
      obtain ⟨t,ht⟩ := RouteBank.destination_mem _ (routeReg reg) (.inl j) a h
      exact ⟨.route t,ht⟩
    | inr j => fin_cases j <;> contradiction
  | handoff i =>
    obtain ⟨t,ht⟩ := handoff_mem _ (bootReg reg) (leafReg reg) _ _ i a h
    exact ⟨.boot t,ht⟩
  | boot i =>
    obtain ⟨t,ht⟩ := LeafBoot.destination_mem _ (bootReg reg) _ _ i a h
    exact ⟨.boot t,ht⟩
  | stack q i =>
    obtain ⟨t,ht⟩ := stack_mem auxiliaryCode _ (LeafBoot.stack (bootReg reg)) _ q i a h
    exact ⟨_,ht⟩

end PairSimulation.LeafImage

end VPVNP
end Computability
end OAI
