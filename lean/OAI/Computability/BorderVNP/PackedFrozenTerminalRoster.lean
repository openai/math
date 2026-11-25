import OAI.Computability.BorderVNP.PackedFrozenTerminalMeasure

/-! # Terminal packet-source volume of the routed seed and selected history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch DeckGrid Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open Diagonal Diagonal.ExternalSew TeamScales Filter CellPacketGeometry.History
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- The row count of the routed seed grid is part of the actual bottom physical rectangle. -/
theorem seed_tiles_le (depth : ℕ) :
    GridHosts.tileCount (Fintype.card (Cube D)) depth ≤ physicalRows (boundaryShape S (depth+1) 0) := by
  have eqn : GridHosts.tileCount (Fintype.card (Cube D)) depth = CoverScale.sites (Cube D) (depth+1) := by
    simp only [GridHosts.tileCount,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]
  rw [eqn]
  exact Nat.le_add_right _ _

/-- Reserved bit pins of the final binding writer, including all zero-width candidates. -/
theorem final_payload_le (shape : Shape) (cells original live w : ℕ) :
    Fintype.card (FinalTies.Row (shape.edges+4*live) live × Fin 9 × Fin w) ≤
      9*routingRows shape cells original live*w := by
  have h : (shape.edges+4*live)*2+live ≤ routingRows shape cells original live := by
    unfold routingRows CellAddressCircuit.count; omega
  simp only [FinalTies.Row,Subdivision.Gates.Old,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool]
  exact (Nat.mul_le_mul_right (9*w) h).trans_eq (by ring)

local notation3 "q" => Fintype.card (Cube D)

/-- The genuine bottom frame may reserve up to a fixed number of disabled slots per tile.
The cumulative chronological record source, all its bit pins, and the actual final binding
rows fit the terminal routing rectangle times a quadratic logarithm. The fixed constant is
chosen before the input length, number of teams, public row IDs and hidden verifier. -/
theorem eventually_seed_roster {a x : ℕ} (scale : EpochScales S a x) (H : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let depth := start-1
      let T := epochs scale.τ n
      let w := 60*logWidth r n
      ∀ {qe qa : ℕ} (order : Fin (GridHosts.tileCount q depth) ≃ (Fin q → Deck (depth+2)))
        (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
        (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
        (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (copies holes : ℕ),
        holes ≤ H*GridHosts.tileCount q depth → ∀ cells original live : ℕ,
        let base := Format.bottom (Seed.rows n r order position channels groups copies) holes w
        let G := epoch S start w base T
        let shape := boundaryShape S start T
        let L := FinalTies.tieSchema (shape.edges+4*live) live w
        G.schema.rows.length+tagWords G.schema+L.rows.length+tagWords L+
          Fintype.card G.Payload+Fintype.card (FinalTies.Row (shape.edges+4*live) live × Fin 9 × Fin w) ≤
          C*routingRows shape cells original live*(logWidth r n)^2 := by
  let seedCap := 9*(2+2*Fintype.card (Direction q))+H
  obtain ⟨C,counts⟩ := eventually_measures S scale seedCap
  refine ⟨3*C+550,?_⟩
  filter_upwards [counts,eventually_ge_atTop 1] with n use hn
  intro r hr start depth T w qe qa order position channels groups copies holes vacant cells original live base G shape L
  let log := logWidth r n
  let R := routingRows shape cells original live
  have pos : 0 < start := Nat.succ_pos _
  have d : depth+1 = start := by change start-1+1 = start; omega
  have tiles : GridHosts.tileCount q depth ≤ physicalRows (boundaryShape S start 0) := d ▸ seed_tiles_le S depth
  have one : 1 ≤ log := by
    rw [show log = Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact (by decide : 1 ≤ Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr]))
  have measured (M : Measure) : M.count G ≤ C*R*log^2 := by
    apply use r hr base M ?_ cells original live
    exact (Seed.bottom_measure_le n r order position channels groups copies holes w H M vacant).trans
      (Nat.mul_le_mul_left _ tiles)
  have row : G.schema.rows.length ≤ C*R*log^2 := measured .rows
  have tag : tagWords G.schema ≤ C*R*log^2 := measured .words
  have payload : Fintype.card G.Payload ≤ C*R*log^2 := measured .payload
  have front : L.rows.length+tagWords L ≤ 10*R*log^2 :=
    (final_roster_le shape cells original live w).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ one))
  have pin := final_payload_le shape cells original live w
  have square : log ≤ log^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right log one
  have last : Fintype.card (FinalTies.Row (shape.edges+4*live) live × Fin 9 × Fin w) ≤ 540*R*log^2 := by
    exact pin.trans ((Nat.mul_le_mul_left (9*R) (Nat.mul_le_mul_left 60 square)).trans_eq (by ring))
  rw [show (3*C+550)*R*log^2 = 3*(C*R*log^2)+10*R*log^2+540*R*log^2 by ring]
  omega

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
