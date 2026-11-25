import OAI.Hierarchy.ProtocolRAMSelectedTape
import OAI.Hierarchy.ProtocolRAMRepairHistogram
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Dropping inactive native rows from the signed histogram -/

namespace Hierarchy.ProtocolRAM.SelectedRows
open AdaptiveProbe AdaptiveProbe.OuterBank RepairHistogram
open scoped BigOperators Classical
noncomputable section
variable {r n : ℕ} {I X : Type*} [Fintype I]

omit [Fintype I] in
theorem Tape.bill (T : Tape r n I) (w : ℕ) :
    cashChange (fun e=>T.kind (T.use e)) (netUnits w (fun e=>T.put (T.use e)) (fun e=>T.take (T.use e)))
      (fun e=>T.weight (T.use e)) ((∑j,T.broadcast (row T.selected j))/w) =
      cashChange T.kind (netUnits w T.put T.take) T.weight ((∑ j,T.broadcast j)/w) := by
  rw [totals T.selected T.broadcast T.quiet]
  exact cashChange_active T.use T.kind w T.put T.take T.weight _ fun _ away=>T.off away

/-- Construct the analytic failed-row receipt from the uncompressed physical
balance, cash and curvature. Its only strict improvement is a local quote at each
selected row. No zeroed or padding row contributes to the claimed density. -/
def Tape.failedRows (T : Tape r n I) (B : OuterBank I X) (before after : X)
    (sites w K cap : ℕ) (ρ γ s : ℝ) (raw : I→ℕ) (width : Fin r→ℕ)
    (balance : ∀ i, B.stock before i+resourceBits T.kind T.put i=raw i+resourceBits T.kind T.take i)
    (remaining : ∀ i,B.stock after i=min (raw i) (cap*w))
    (price : B.cash after≤B.cash before+cashChange T.kind (netUnits w T.put T.take) T.weight ((∑j,T.broadcast j)/w)+
      pairing (bitStock w (spillBits cap w raw)) B.box)
    (many : ρ*sites≤T.selected.card) (positive : ∀j∈T.selected,0<width j)
    (size : ∀j∈T.selected,2*(K*width j)≤w)
    (quote : let x := maximizer B.a B.M s B.coefficient B.box (B.units w before)
             let p := activePrice T.kind T.weight x
             ∀ j∈T.selected, (∑ e, (T.put (T.enum ⟨j,e⟩):ℝ)*p (T.enum ⟨j,e⟩))+T.broadcast j+
               (AdaptiveProbe.copied K (width j) w:ℝ)*(width j*γ/2)≤∑ e,(T.take (T.enum ⟨j,e⟩):ℝ)*p (T.enum ⟨j,e⟩))
    (curvature : (∑ i,(stockChange T.kind (netUnits w T.put T.take) i)^2/(4*s*B.a))≤(sites:ℝ)*ρ*γ/(8*K)) :
    B.FailedRows sites w K cap ρ γ s before after where
  rows := T.selected.card
  ports := fun j=>T.ports (row T.selected j)
  kind := fun e=>T.kind (T.use e)
  installed := fun e=>T.put (T.use e)
  consumed := fun e=>T.take (T.use e)
  weight := fun e=>T.weight (T.use e)
  broadcast := fun j=>T.broadcast (row T.selected j)
  width := fun j=>width (row T.selected j)
  raw := raw
  stock := fun i=>by
    rw [resourceBits_active T.use T.kind T.put (fun _ h=>(T.off h).1),
      resourceBits_active T.use T.kind T.take (fun _ h=>(T.off h).2)]
    exact balance i
  retained := remaining
  paid := by rw [T.bill w]; exact price
  density := many
  width_pos := fun j=>positive _ (row_mem _ j)
  width_fits := fun j=>size _ (row_mem _ j)
  quotes := fun j=>quote _ (row_mem _ j)
  curvature := by simpa only [T.delta] using curvature

end
end Hierarchy.ProtocolRAM.SelectedRows

end OAI
