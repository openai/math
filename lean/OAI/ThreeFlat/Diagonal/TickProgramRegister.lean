import OAI.ThreeFlat.Diagonal.PhysicalProgramRecords
import OAI.ThreeFlat.Diagonal.TickGroupRegister

namespace OAI
/-! # The actual executable histogram record and terminal wire allocation in AUX -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage.Program.RecordTable

open TickAuxiliary HistoryContraction
variable {F : Type} [Field F] {d l K W a capacity : ℕ} {A : State d l} {r : Run F A} {sizes : List ℕ}
variable (Q : RecordTable r K W sizes)

def groupRegister (allocated : 1+capacity ≤ a)
    (wires : ∀ h, sizes.sum*K*W+(r.terminalLayer h).state.widthSum ≤ capacity) :
    GroupRegister r.plan Q.codes (fun h => (r.terminalLayer h).state.widthSum) a where
  capacity := capacity
  fits := allocated
  room h := by rw [Q.write_size]; exact wires h

/-- Admission reads the same variable-length wire suffix used by the terminal factors. -/
theorem register_decodes (allocated : 1+capacity ≤ a)
    (wires : ∀ h, sizes.sum*K*W+(r.terminalLayer h).state.widthSum ≤ capacity)
    (v : Plan.Terminal r.plan (fun h => (r.terminalLayer h).state.widthSum)) :
    let R := Q.groupRegister allocated wires
    decode r.plan Q.codes (fun h => (r.terminalLayer h).state.widthSum) R.base (R.ready v) = some v := by
  dsimp only
  exact (Q.groupRegister allocated wires).decode_ready (n:=0) (by
    change 1+capacity+2*0 ≤ a
    simpa using allocated) v


end ThreeFlat.Diagonal.PhysicalStage.Program.RecordTable

end
end OAI
