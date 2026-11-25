import OAI.Computability.BorderVNP.DiagonalFrozenPacketInputs
import OAI.Computability.BorderVNP.DiagonalNativeGeometryWindow

/-! # A single choice of public table ceiling and signed directory bounds -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Cover.AddressCircuit Epoch Packing DeckGrid PackedHistoryCircuit
open Packing.Inherited FrozenTape CellPacketGeometry CellPacketGeometry.History
open CellPacketGeometry.LiveWords CellSparse.Packet Shortening.PublicCapacity
open ExternalSew ExternalSew.RowTrace TeamContraction PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
local notation "axes" => Fintype.card (Cube D)

/-- Choose the size constant of the actual public geometry table before the
two stretch exponents or any later field data. At every sufficiently large
degree both the native interpretation window and the slot/word certificates
for the same real signed output are available together. -/
theorem EpochScales.exists_signed_output_calibration {a extra : ℕ} (scales : EpochScales S a extra) (g E controlsCap : ℕ) :
    ∃ A : ℕ, ∀ {deg Q a₀ b₀ j : ℕ} (b : JointSchedule scales (E+1) deg Q a₀ b₀ j), 5*(E+2) ≤ deg →
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let tiles := GridHosts.tileCount axes d
      let T := epochs scales.τ n
      let cells := CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T)
      let copies := TeamScales.width n scales.α
      let R := b.physical.teamsPred n
      NativeGeometryWindow (8*(11920000+1500000+16008100*A+controlsCap)) (4*(E+2)) n r
        (b.physical.word n) (R+1) tiles ((fan S)^T*tiles)
        (routingRows (boundaryShape S (d+1) T) cells ((fan S)^T*tiles) ((R+1)*tiles)) ∧
      ∀ {teams time pins link inner : ℕ} {Edge : Type} (G : Wiring teams r time pins link inner n Edge)
        (order : Fin tiles ≃ (Fin axes → Deck (d+2)))
        (position : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
        (dir : Directory.Layout) (number : e.Entry → ℕ),
        let physical := {dir with sites := tiles, entries := (fan S)^T*tiles}
        SignedPacketInputBounds S (d+1) T cells ((R+1)*tiles) (60*logWidth r n) (b.physical.word n)
          (logWidth r n) E A g (Boundary.seedFormat G order position copies) physical rfl number := by
  obtain ⟨A,selected⟩ := scales.exists_frozen_packet_bounds g E
  refine ⟨A,?_⟩
  intro deg Q a₀ b₀ j b power
  let U := 8*(11920000+1500000+16008100*A+controlsCap)
  have measured := b.eventually_native_geometry_window U (4*(E+2)) (by omega)
  filter_upwards [measured,selected b] with n window inputs
  exact ⟨window,inputs⟩

end Diagonal

end BorderVNP
end Computability
end OAI
