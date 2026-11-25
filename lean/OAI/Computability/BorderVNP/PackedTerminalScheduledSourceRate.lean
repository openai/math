import OAI.Computability.BorderVNP.PackedTerminalSewnRoster
import OAI.Computability.BorderVNP.PackedHistoryBoxVolume

/-! # Uniform signed packet volume on the calibrated processor grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch DeckGrid Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open PackedHistoryCircuit.Normalized.EnrichedOuter Diagonal Diagonal.ExternalSew TeamScales Filter
open CellPacketGeometry.History
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)
local notation "q" => Fintype.card (Cube D)

/-- Sparse source words of the *actual* signed terminal including the live
site-sewing interval records, final absolute binding tape, scheduled one-copy
paid/original boxes, transmitted original pointer bank and the spare report
cell. The rectangle uses the genuine transmitted original count. -/
theorem eventually_scheduled_sourceVolume {a x : ℕ} (scale : EpochScales S a x) (holesCap g digitsCap digitsDegree : ℕ) :
    ∃ A : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let depth := start-1
      let T := epochs scale.τ n
      let w := 60*logWidth r n
      ∀ {qe qa : ℕ} (order : Fin (GridHosts.tileCount q depth) ≃ (Fin q → Deck (depth+2)))
        (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
        (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
        (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (copies holes : ℕ),
        holes≤holesCap*GridHosts.tileCount q depth → ∀ cells live : ℕ,
        let shape := boundaryShape S start T
        ∀ (dir : Directory.Layout) (count : dir.entries=(fan S)^T*dir.sites) (number : e.Entry → ℕ)
          (positive : 0<shape.sites) (digits : ℕ), digits≤digitsCap*(logWidth r n)^digitsDegree →
          let base := Format.bottom (Seed.rows n r order position channels groups copies) holes w
          let G := epoch S start w base T
          let F := G.schema.append (Sewn.schema (2*shape.edges+6*live) w)
          let L := FinalTies.tieSchema (shape.edges+4*live) live w
          let boxes := scheduledBoxes dir count number positive
          let report := FinalReports.Spare.reports (C:=cells) (g:=g) (digits:=digits) (E:=Fin dir.entries)
          sourceVolume F L boxes report ≤ A*routingRows shape cells dir.entries live*(logWidth r n)^(max 2 digitsDegree) := by
  obtain ⟨A,roster⟩ := eventually_sewn_roster S scale holesCap
  refine ⟨(3+BoxRoster.paidWordLimit e)*(A+4+g*(1+digitsCap)),?_⟩
  filter_upwards [roster,eventually_ge_atTop 1] with n issued hn
  intro r hr start depth T w qe qa order position channels groups copies holes hholes cells live shape
    dir count number positive digits hd base G F L boxes report
  let R := routingRows shape cells dir.entries live
  let H := logWidth r n
  let d := max 2 digitsDegree
  let U := R*H^d
  have pins := issued r hr order position channels groups copies holes hholes cells dir.entries live
  change F.rows.length+tagWords F+L.rows.length+tagWords L ≤ A*R*H^2 at pins
  have hh : 1≤H := (GeometryAdviceRate.indexWidths hr hn).1
  have one : 1≤R := by unfold R routingRows; omega
  have sites : shape.sites≤R := by unfold R routingRows CellAddressCircuit.count; omega
  have cs : cells≤R := by unfold R routingRows CellAddressCircuit.count; omega
  have orig : dir.entries≤R := by unfold R routingRows; omega
  have large : R≤U := Nat.le_mul_of_pos_right _ (Nat.succ_le_of_lt (pow_pos hh _))
  have digitsPower : H^digitsDegree≤H^d := Nat.pow_le_pow_right hh (le_max_right ..)
  have schemaPower : H^2≤H^d := Nat.pow_le_pow_right hh (le_max_left ..)
  have cg : cells*g≤g*U := (Nat.mul_le_mul_right g (cs.trans large)).trans_eq (Nat.mul_comm ..)
  have cd : cells*g*digits ≤ g*digitsCap*U := by
    calc
      _ ≤ (R*g)*(digitsCap*H^digitsDegree) := Nat.mul_le_mul (Nat.mul_le_mul_right g cs) hd
      _ ≤ (R*g)*(digitsCap*H^d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ digitsPower)
      _ = _ := by dsimp only [U]; ring
  have charge : 1+shape.sites+cells*(1+g*(1+digits))+F.rows.length+tagWords F+L.rows.length+tagWords L+dir.entries ≤
      (A+4+g*(1+digitsCap))*U := by
    have schema : F.rows.length+tagWords F+L.rows.length+tagWords L ≤ A*U :=
      pins.trans ((Nat.mul_le_mul_left _ schemaPower).trans_eq (by dsimp only [U]; ring))
    nlinarith only [one.trans large,sites.trans large,cs.trans large,orig.trans large,cg,cd,schema]
  exact (scheduledBoxes_sourceVolume (g:=g) (digits:=digits) (C:=cells) dir count number positive F L).trans
    ((Nat.mul_le_mul_left _ charge).trans_eq (by dsimp only [U,R,H,d]; ring))

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
