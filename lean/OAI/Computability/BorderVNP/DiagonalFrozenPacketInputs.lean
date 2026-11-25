import OAI.Computability.BorderVNP.PackedTerminalSignedSelectedRange
import OAI.Computability.BorderVNP.PackedFrozenSeedInitial
import OAI.Computability.BorderVNP.DiagonalJointSchedule
import OAI.Computability.BorderVNP.PackedFrozenNativePort

/-! # Inputs of the signed packet at its selected physical degree and team count -/

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

/-- The width and volume facts used by the literal signed packet for its own
starting format and original descriptor directory. The parameters permit a
proof transport when the selected level or volume is rewritten. -/
def SignedPacketInputBounds (S : SiteSchedule e) (start T cells live short native H E A hooks : ℕ)
    (seed : Format) (dir : Directory.Layout) (count : dir.entries=(fan S)^T*dir.sites) (number : e.Entry → ℕ) : Prop :=
  let shape := boundaryShape S start T
  let rows := routingRows shape cells dir.entries live
  let cap := ProgramSchemas.signedTagCapacity (e:=e)
  let history := ProgramSchemas.epoch S start short seed T
  let source := history.schema.append (Sewn.schema (2*shape.edges+6*live) short)
  let lastTape := FinalTies.tieSchema (shape.edges+4*live) live native
  ∀ positive : 0<shape.sites,
    let boxes := scheduledBoxes dir count number positive
    let report := FinalReports.Spare.reports (C:=cells) (g:=hooks) (digits:=native) (E:=Fin dir.entries)
    let priv := FinalReports.Spare.priv (C:=cells) (g:=hooks) (digits:=native) (E:=Fin dir.entries)
    let volume := sourceVolume source lastTape boxes report
    volume ≤ A*rows*H^(max 2 (E+2)) ∧
    (256*volume+2*rows+1 < 2^native ∧ keyWidth axes (EnrichedOuter.depth S start T+1) ≤ native ∧
      Nat.clog 2 rows ≤ native ∧ short ≤ native ∧ cells+1 < 2^short ∧ shape.sites ≤ 2^short) ∧
    (∀ j, source.width j ≤ native) ∧ (∀ j, lastTape.width j ≤ native) ∧
    ∃ sh : ∀ j, (source.tags j).length ≤ cap, ∃ th : ∀ j, (lastTape.tags j).length ≤ cap,
    let tpl := template source lastTape boxes sh th priv report
    let len := (roster shape.sites source lastTape).length
    shape.sites < 2^native ∧ cells < 2^native ∧ len < 2^native ∧
    tpl.publicDepth ≤ native ∧ tpl.chunkDepth ≤ native ∧ tpl.recordDepth ≤ native ∧
    Nat.clog 2 (len+(cells+1)) ≤ native ∧ Nat.clog 2 ((shape.sites+1)+len) ≤ native

/-- One constant chosen before the processor exponents applies to all input
wiring choices and original pointer directories. The proof uses the scheduled
number of teams, the actual source format with zero additional holes and the
true RAM word; there is no premise bounding the emitted source volume. -/
theorem EpochScales.exists_frozen_packet_bounds {a extra : ℕ} (scales : EpochScales S a extra) (g E : ℕ) :
    ∃ A : ℕ, ∀ {deg Q a₀ b₀ j : ℕ} (b : JointSchedule scales (E+1) deg Q a₀ b₀ j),
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let tiles := GridHosts.tileCount axes d
      let T := epochs scales.τ n
      let cells := CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T)
      let copies := TeamScales.width n scales.α
      let R := b.physical.teamsPred n
      ∀ {teams time pins link inner : ℕ} {Edge : Type} (G : Wiring teams r time pins link inner n Edge)
        (order : Fin tiles ≃ (Fin axes → Deck (d+2)))
        (position : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
        (dir : Directory.Layout) (number : e.Entry → ℕ),
        let physical := {dir with sites := tiles, entries := (fan S)^T*tiles}
        SignedPacketInputBounds S (d+1) T cells ((R+1)*tiles) (60*logWidth r n) (b.physical.word n)
          (logWidth r n) E A g (Boundary.seedFormat G order position copies) physical rfl number := by
  obtain ⟨A,range⟩ := ProgramSchemas.eventually_signed_directory_bounds S scales 0 g E
  refine ⟨A,?_⟩
  intro deg Q a₀ b₀ j b
  filter_upwards [range,eventually_ge_atTop 1] with n inputs hn
  intro r d tiles T cells copies R teams time pins link inner Edge G order position dir number physical
  let start := CoverScale.initialDepth (Cube D) r n
  have level : d+1=start := by
    change start-1+1=start
    exact Nat.sub_add_cancel (Nat.succ_pos _)
  have card : tiles = CoverScale.sites (Cube D) start := (seedPortCount (D:=D) d).trans (congrArg _ level)
  have team : R+1 = TeamScales.teams scales.α scales.τ (fan S) n := (b.sizes hn).1
  have size : b.physical.word n = (logWidth r n)^(E+2) := rfl
  let orig := (groupedGridRows G axes d order position copies).edge
  let group := (Equiv.refl (Fin tiles)).toEmbedding
  have source := inputs r (stretch_one ..) order position orig group copies 0 (Nat.zero_le _) physical
    (show physical.sites=CoverScale.sites (Cube D) start from card) rfl number
  change SignedPacketInputBounds S (d+1) T (CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T))
    ((R+1)*tiles) _ _ _ _ _ _ _ _ _ _
  rw [level,team,card,size]
  exact source

end Diagonal

end BorderVNP
end Computability
end OAI
