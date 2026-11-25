import OAI.ThreeFlat.Diagonal.TraceCostFormula
import OAI.ThreeFlat.Diagonal.TraceStaticPorts

namespace OAI
/-! # Number of row ports and total shared variables -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP TraceProgram

theorem card_ports (w p r k d : ℕ) :
    Fintype.card (Port w p r k d) = portCount w p r k d := by
  simp [Port,Ctrl,Outer,TraceRowPackets.MemoryControl,TraceRowPackets.InitControl,
    TraceMemoryCircuit.MemoryControl,TraceUniformRow.Port,TracePhysical.Port,portCount,Nat.add_assoc]

end ThreeFlat.Diagonal.TraceStaticRow

namespace ThreeFlat.Diagonal.TraceVolume

open Computability.VPVNP TraceStaticRow

/-- The shared CPU, memory-sort, boundary, and replicated instruction
variables are all bounded by the local port count times the number of rows. -/
theorem shared_le {w p r k d f : ℕ} (hf : f ≤ 2*2^d) :
    TraceUniformRow.SharedCount w p r k d f ≤ 2^d*portCount w p r k d := by
  rw [TraceUniformRow.SharedCount,← TracePhysical.sharedCount_card]
  unfold TracePhysical.sharedCount TraceUniformRow.CopyCount
  let T := 2^d
  let L := RAMLayout.layerCount d
  let cpu := (5+r)*(w+1)
  let recordWidth := 7*(w+1)
  let text := (1+6*p+k)*w
  change f*cpu + (L*(T*(2*recordWidth)) + (T-1)*recordWidth) + T*text ≤ _
  calc
    _ ≤ (2*T)*cpu + (L*(T*(2*recordWidth)) + T*recordWidth) + T*text := by gcongr; first | exact hf | omega
    _ = T*(2*cpu+L*(2*recordWidth)+recordWidth+text) := by ring
    _ ≤ _ := Nat.mul_le_mul_left T (by
      change 2*cpu+L*(2*recordWidth)+recordWidth+text ≤
        (3*cpu + (2*w+(L*(2*(2*recordWidth))+2*recordWidth))) + 2*text +
          ((2*(2+2*(w+1))+((d+2)*2+1))+(2+(2+(2+text))))
      ring_nf
      omega)

end ThreeFlat.Diagonal.TraceVolume

end OAI
