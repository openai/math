import OAI.Computability.VPVNP.PairSimulationLeafScalarTable

/-!
# Initializing all scalar stacks of the actual auxiliary RAM

Starting at the first allocation row, the only data-dependent inputs are
the real source registers, the arena base and capacity. The resulting
private memory function is determined on every address. The incident
stack is empty for the ensuing half-wire copy.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup

open BurstRAM PrivateRAM RAMTape StackMachine PrimedCounter.GuessWord LeafRegisterBank
open scoped Fin.CommRing

set_option synthInstance.maxSize 10000

variable {A : PrimedInputRAM.Lengths} {n a H s w d e p r k : ℕ} {Q : PrimedInputRAM.Layout A n a H w}
variable (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (v : CursorNetwork.Position d) (buf : CursorNetwork.Buffers d (2^e) w)

/-- A private stack port of the concrete leaf site processor with 52 registers and 34 public
operands. -/
abbrev ScalarPort := LeafStartup.Port 52 34
/-- The concrete register bank for filling the scalar ports from site data and the validator's
34 public operands. -/
abbrev ScalarReg := LeafRegisterBank.Reg ScalarPort 34
/-- Instruction labels for allocating, staging and filling the concrete validator's scalar
stacks. -/
abbrev ScalarLabel := LeafPortTable.Label ScalarPort

/-- Enumerate all concrete scalar ports by consecutive indices for the startup traversal. -/
noncomputable def portOrder : Fin (Fintype.card ScalarPort) ≃ ScalarPort := (Fintype.equivFin ScalarPort).symm

/-- The list of all scalar ports visited once, in the order used to allocate and fill the
private stacks. -/
noncomputable def scalarRows := List.ofFn portOrder

/-- The scalar stacks encoded from the auxiliary site's input, its half-wire buffers and the
counter's public operands, with the incident stack awaiting its separate copy. -/
noncomputable def scalarInput : Stacks ScalarPort := scalarBank field (auxiliary D hw hc v buf) D.pub

/-- Exact instruction count for allocating and filling the concrete list of scalar ports at
this auxiliary site. -/
noncomputable def scalarTicks := LeafPortTable.cost field (auxiliary D hw hc v buf) D.pub scalarRows

theorem incident_install :
    Function.update (scalarInput D hw hc v buf) (LeafLoadedBank.incidentPort 52 34)
      (List.ofFn (CursorNetwork.incidentBuffer v buf)) = bank 52 (auxiliary D hw hc v buf) D.pub := by
  have h := LeafLoadedBank.install_incident (r := 52) (auxiliary D hw hc v buf) D.pub
  simpa only [scalarInput,auxiliary,sends_incident] using h

/-- The whole allocation-and-scalar pass in the enclosing machine, including
its exact scratch update and preservation of all other native registers. -/
theorem scalar_start (M : Machine w p r k) (reg : ScalarReg ↪ Fin r) (pc : ScalarLabel → Fin p)
    (done : Fin p) (base cap : ℕ) (fit : base + Fintype.card ScalarPort*cap < 2^w)
    (link : ∀ j, M.code (pc j) = LeafPortTable.instruction field pc reg done scalarRows j)
    (c : Config w p r)
    (entry : c.pc = LeafPointers.next scalarRows (fun a i => pc (.pointer a i)) (pc (.finish 0)))
    (hbase : c.reg (LeafFill.pointers (load reg) .cursor) = (base : Word w))
    (hcap : c.reg (LeafFill.pointers (load reg) .stride) = (cap : Word w))
    (inputs : ∀ j, c.reg (reg (.inr j)) = sourceWord (auxiliary D hw hc v buf) D.pub j)
    (room : ∀ a, (scalarInput D hw hc v buf a).length ≤ cap) :
    let L := Layout.consecutive portOrder.symm.toEmbedding base cap fit
    ∃ out, Prefix M c (List.replicate (scalarTicks D hw hc v buf) .tick) out ∧ out.pc = done ∧
      Represents L (stack reg) out (scalarInput D hw hc v buf) ∧
      Staging.Sources (auxiliary D hw hc v buf) D.pub (out.reg ∘ stage reg) ∧
      out.persistent = c.persistent ∧ (∀ i, i ∉ Set.range reg → out.reg i = c.reg i) ∧
      out.privateMem = LeafLoadedBank.memory L (scalarInput D hw hc v buf) c.privateMem := by
  intro L
  have hl (i) : L.base (portOrder i) = base + i.val*L.capacity := by simp [L,Layout.consecutive]
  obtain ⟨out,run,hpc,rep,ready,state,regs,mem⟩ := LeafPortTable.startup field pc reg done M portOrder L base hl
    (auxiliary D hw hc v buf) D.pub link c entry hbase hcap inputs room
  refine ⟨out,?_,hpc,rep,ready,state,regs,LeafLoadedBank.memory_eq L _ _ _ rep.cells room mem⟩
  simpa only [scalarTicks,LeafPortTable.cost,scalarRows,List.length_ofFn] using run

end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
