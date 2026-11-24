import OAI.Computability.VPVNP.PairSimulationLeafIncidentMachine
import OAI.Computability.VPVNP.PrivateRAMRegisterOperands

/-! # Register destinations of the cursor-zero incident loader -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentMachine

open BurstRAM PrivateRAM RegisterOperands

variable {W p r k : ℕ}

private def Contained {n : ℕ} (reg : Fin n ↪ Fin r) (op : Instr W p r k) :=
  ∀ a, destination op = some a → a ∈ Set.range reg

private theorem widen {a b : ℕ} (u : Fin a ↪ Fin b) (reg : Fin b ↪ Fin r) {op : Instr W p r k}
    (h : Contained (u.trans reg) op) : Contained reg op := by
  intro j hj
  obtain ⟨i,hi⟩ := h j hj
  exact ⟨u i,hi⟩

private theorem mover (source : LeafFieldCopy.Source) (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r)
    (done : Fin p) (i : Fin 5) : Contained (W := W) (k := k) reg (LeafFieldCopy.instruction source pc reg done i) := by
  intro a ha
  cases source <;> fin_cases i <;> first | exact ⟨_, Option.some.inj ha⟩ | contradiction

private theorem prepare (port : Option CursorNetwork.LocalPort) (pc : Fin 2 → Fin p)
    (reg : Fin 11 ↪ Fin r) (done : Fin p) (i : Fin 2) :
    Contained (W := W) (k := k) reg (LeafIncidentLoad.prepare port pc reg done i) := by
  intro a ha
  cases port <;> fin_cases i <;> exact ⟨_, Option.some.inj ha⟩

private theorem classifier (pc : Fin 6 → Fin p) (reg : Fin 4 ↪ Fin r) (done : Fin p) (i : Fin 6) :
    Contained (W := W) (k := k) reg (LeafSuccessorClass.instruction pc reg done i) := by
  intro a ha
  fin_cases i <;> first | exact ⟨_, Option.some.inj ha⟩ | contradiction

private theorem successor (pc : LeafSuccessorFields.Stage → Fin p) (reg : Fin 20 ↪ Fin r) (done : Fin p)
    (s : LeafSuccessorFields.Stage) : Contained (W := W) (k := k) reg (LeafSuccessorFields.instruction pc reg done s) := by
  cases s with
  | classify recv i => exact widen _ reg (classifier _ _ _ i)
  | prepare recv use i => exact widen _ reg (prepare _ _ _ _ i)
  | move recv use i => exact widen _ reg (widen _ _ (mover _ _ _ _ i))
  | sender recv => intro a ha; cases recv <;> exact ⟨_,Option.some.inj ha⟩
  | _ => intro a ha; first | exact ⟨_,Option.some.inj ha⟩ | contradiction

private theorem sort (pc : LeafSortFields.Stage → Fin p) (reg : Fin 17 ↪ Fin r) (done : Fin p)
    (s : LeafSortFields.Stage) : Contained (W := W) (k := k) reg (LeafSortFields.instruction pc reg done s) := by
  cases s with
  | prepare recv side i =>
    simp only [LeafSortFields.instruction]
    exact widen (Fin.castAddEmb 6) reg (prepare _ _ (LeafSortFields.subRegs reg) _ i)
  | move recv side i =>
    simp only [LeafSortFields.instruction]
    exact widen (Fin.castAddEmb 6) reg (widen (Fin.castAddEmb 6) (LeafSortFields.subRegs reg)
      (mover .resident _ (LeafIncidentLoad.copyRegs (LeafSortFields.subRegs reg)) _ i))
  | _ => intro a ha; first | exact ⟨_,Option.some.inj ha⟩ | contradiction

private theorem core (pc : LeafIncidentCore.Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p)
    (s : LeafIncidentCore.Stage) : Contained (W := W) (k := k) reg (LeafIncidentCore.instruction pc reg done s) := by
  rcases s with s | i | s
  · exact widen _ reg (successor _ _ _ s)
  · intro a ha; fin_cases i <;> exact ⟨_,Option.some.inj ha⟩
  · exact widen _ reg (sort _ _ _ s)

/-- Every written register is an operand of the loader's actual embedding. -/
theorem destination_mem (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) (i : Stage) (a : Fin r)
    (ha : destination (instruction (W := W) (k := k) pc reg done i) = some a) : a ∈ Set.range reg := by
  cases i with
  | inl i =>
    change destination (LeafIncidentGeometry.emit reg _ LeafIncidentGeometry.rows[i]) = some a at ha
    generalize LeafIncidentGeometry.rows[i] = line at ha
    obtain ⟨j,rhs⟩ := line
    cases rhs <;> exact ⟨j,Option.some.inj ha⟩
  | inr i => exact core _ _ _ i a ha

end PairSimulation.LeafIncidentMachine

end VPVNP
end Computability
end OAI
