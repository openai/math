import OAI.Computability.BorderVNP.PackedSewnRecordEmitter
import OAI.Computability.BorderVNP.PackedFrozenTerminalRoster

/-! # The actual appended sewing interval rows in the public chronological tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open CellPacketGeometry.History PackedHistoryCircuit.Normalized.SelectedSchedule Shortening.PublicCapacity
open scoped BigOperators

namespace Sewn

open private tags count from OAI.Computability.BorderVNP.PackedSewnRecordEmitter

/-- Each of the two row shapes contributes once at each allocated interval
ordinal, irrespective of which physical owner is active. -/
theorem schema_scalar_volume (n w : ℕ) :
    (schema n w).rows.length + tagWords (schema n w) = 17*n := by
  have fields (xs : List (Fin n)) :
      (((xs.flatMap fun i => [(i,false),(i,true)]).map fun r => ((schema n w).tags r).length).sum) =
        15*xs.length := by
    induction xs with
    | nil => simp
    | cons i tail ih =>
      change 6+ (9+(((tail.flatMap fun i => [(i,false),(i,true)]).map fun r => ((schema n w).tags r).length).sum)) =
        15*(tail.length+1)
      omega
  have h := fields (List.finRange n)
  simp only [List.length_finRange] at h
  have rows : (schema n w).rows.length = 2*n := by
    simp [schema,List.length_flatMap,Nat.mul_comm]
  unfold tagWords
  rw [rows]
  change 2*n+(((List.finRange n).flatMap fun i => [(i,false),(i,true)]).map fun r => ((schema n w).tags r).length).sum =
    17*n
  omega

end Sewn

namespace ProgramSchemas

open Crossing Cover Epoch DeckGrid PackedHistoryCircuit PackedHistoryCircuit.Normalized
open Diagonal Diagonal.ExternalSew TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- Both true sparse schemas consumed by the signed and field packet join:
the complete chosen history followed by its sewn endpoint intervals, then
the final absolute binding rows. The constant is uniform in processor count,
degree of padding and every realized public or private input branch. -/
theorem eventually_sewn_roster {a x : ℕ} (scale : EpochScales S a x) (H : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let depth := start-1
      let T := epochs scale.τ n
      let w := 60*logWidth r n
      ∀ {qe qa : ℕ} (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) depth) ≃ (Fin (Fintype.card (Cube D)) → Deck (depth+2)))
        (position : (Fin (Fintype.card (Cube D)) → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
        (channels : ((Fin (Fintype.card (Cube D)) → Deck (depth+2)) × Direction (Fintype.card (Cube D))) ↪ Fin qe)
        (groups : Fin (GridHosts.tileCount (Fintype.card (Cube D)) depth) ↪ Fin qa) (copies holes : ℕ),
        holes ≤ H*GridHosts.tileCount (Fintype.card (Cube D)) depth → ∀ cells original live : ℕ,
        let base := Format.bottom (Seed.rows n r order position channels groups copies) holes w
        let G := epoch S start w base T
        let shape := boundaryShape S start T
        let F := G.schema.append (Sewn.schema (2*shape.edges+6*live) w)
        let L := FinalTies.tieSchema (shape.edges+4*live) live w
        F.rows.length+tagWords F+L.rows.length+tagWords L ≤
          C*routingRows shape cells original live*(logWidth r n)^2 := by
  obtain ⟨C,accepted⟩ := eventually_seed_roster S scale H
  refine ⟨C+17,?_⟩
  filter_upwards [accepted,eventually_ge_atTop 1] with n fit hn
  intro r hr start depth T w qe qa order position channels groups copies holes h cells original live base G shape F L
  let R := routingRows shape cells original live
  have prior := fit r hr order position channels groups copies holes h cells original live
  change G.schema.rows.length+tagWords G.schema+L.rows.length+tagWords L+_+_ ≤ C*R*(logWidth r n)^2 at prior
  have slots : 2*shape.edges+6*live ≤ R := by unfold R routingRows CellAddressCircuit.count; omega
  have sew := Sewn.schema_scalar_volume (2*shape.edges+6*live) w
  have pow : 1≤(logWidth r n)^2 := Nat.succ_le_of_lt (pow_pos (GeometryAdviceRate.indexWidths hr hn).1 _)
  have newCap := Nat.mul_le_mul_left 17 (slots.trans (Nat.le_mul_of_pos_right R pow))
  dsimp only [F]
  rw [Schema.append_length,Schema.append_words]
  change _ ≤ (C+17)*R*(logWidth r n)^2
  have bound : (C+17)*R*(logWidth r n)^2 = C*R*(logWidth r n)^2+17*(R*(logWidth r n)^2) := by ring
  rw [bound]
  omega

end ProgramSchemas
end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
