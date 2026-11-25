import OAI.Computability.BorderVNP.DiagonalLocatedSignedGrid

/-! # The actual original block and retained program fit the short frozen history words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover Epoch Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open Shortening.PublicCapacity EnrichedOuter ExternalSew TeamScales TeamContraction ProcessorSlots RoutingISA RoutingISA.Evaluator
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar FieldProcessor
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K F : Type} [Field F] [Field K] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {cube : FixedCube K} {a E p Q A B j : ℕ} {s : EpochScales S (cube.pred+1) a}
    {b : JointSchedule.{0} s (E+1) p Q A B j} {n header : ℕ}

/-- Taking the numerical certificate at the short word bounds the entire loaded
program. It also bounds the original replicated block inside the actual base mass. -/
theorem LocatedSignedGridAt.source_bounds (grid : LocatedSignedGridAt cube b header n) :
    let r := stretch b.ρ n
    let d := CoverScale.initialDepth (Cube D) r n-1
    let copies := width n s.α
    let short := 60*logWidth r n
    let L := S.publicProgramFactor^epochs s.τ n*initialMass (D:=D) n r d copies header
    copies*GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d < 2^short ∧ 15*L < 2^short := by
  intro r d copies short L
  let axes := Fintype.card (Cube D)
  let deg := Fintype.card (Direction axes)
  let K₀ := seedBoxCapacity n r axes d deg
  let H := seedChannelWidth n r axes d
  let desc := seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget K₀)
  have cap : GridHosts.inputBlockWidth r n axes d ≤ K₀ := by dsimp only [K₀,seedBoxCapacity]; omega
  have block : copies*GridHosts.inputBlockWidth r n axes d ≤ initialMass (D:=D) n r d copies header := by
    have h : GridHosts.inputBlockWidth r n axes d ≤ 2*K₀+desc+(2*deg+1)*H := by omega
    change _ ≤ seedPublicBase deg+12+810487*K₀+copies*(2*K₀+desc+(2*deg+1)*H)
    exact (Nat.mul_le_mul_left copies h).trans (Nat.le_add_left _ _)
  have positive : 0 < S.publicProgramFactor := by
    unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor
    positivity
  have loaded : initialMass (D:=D) n r d copies header ≤ L := Nat.le_mul_of_pos_left _ (Nat.pow_pos positive)
  have raw := (grid.packetNumerals short le_rfl).operands
  have lower (mass site scalar w : ℕ) (hr : max (15*mass) site+scalar+1<2^w) : 15*mass<2^w := by omega
  have room : 15*L < 2^short := lower L _ _ short raw
  exact ⟨block.trans_lt (loaded.trans_lt (by omega)),room⟩

end Diagonal

end BorderVNP
end Computability
end OAI
