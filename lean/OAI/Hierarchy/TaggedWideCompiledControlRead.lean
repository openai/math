import OAI.Hierarchy.TaggedWideDateOverlap
import OAI.Hierarchy.TaggedWideControlValues

namespace OAI
/-! # The five original control operands read from physical chronological role tables -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage.CoreBoard.HistoryRoles WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.RAM DescriptorExpr
open Tagged PassiveWindow
open scoped Classical Fin.CommRing BigOperators
variable {S W D cap : ℕ} {s : Fin S}

theorem aperture_geometry {N : ℕ} (m : Memory W) (reg : Word W) (ends : Fin N→Chord S) (qty : Fin N→ℕ)
    (bounded : ∀i,qty i≤cap) (slot : EndsAt ends qty s ↪ Fin D) {t : Widths S}
    (shape : installedWidths ends qty=t) (row : Fin D→LocalPrefix.Columns)
    (neighbors : PacketTurns.NeighborReads m reg (carried ends qty s bounded slot shape)
      (fun i=>(row i).width) (fun i=>(row i).opposite)) (room : ∀p : ((portGraph S).Port s),t p.val.1<2^W) :
    ApertureGeometry m reg (carried ends qty s bounded slot shape) row := by
  let o:=carried ends qty s bounded slot shape
  refine ⟨neighbors,seat_owned ends qty s bounded slot shape,size_sum ends qty s bounded slot shape,?_⟩
  intro i
  change (o.owner i).elim 0 (fun p=>t p.val.1)<2^W
  cases h:o.owner i with
  | none=>exact Nat.two_pow_pos _
  | some p=>exact room p

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
