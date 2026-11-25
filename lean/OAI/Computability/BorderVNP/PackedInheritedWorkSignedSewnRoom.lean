import OAI.Computability.BorderVNP.PackedInheritedWorkSewnCapacity
import OAI.Computability.BorderVNP.DiagonalEnrichedSewnTagModels
import OAI.Computability.BorderVNP.PackedBankPublicHistory

/-! # Final address space of the signed sewn site programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch Inherited Inherited.WorkWords PhysicalEpochs CellAddresses
open BorderVNP.Epoch.Round
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000

universe u

variable {D m start T : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r t pins link inner n copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {deep : S.floor+1+S.drop*T ≤ start} (count : (fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (GridHosts.tileCount axes gridDepth))
      (fun _ => copies*GridHosts.inputBlockWidth r n axes gridDepth) shape W j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)
    {np : ℕ} (oldPort : (Fin ((fan S)^T) × Fin (GridHosts.tileCount axes gridDepth)) ↪ Fin np)
    (hp : (fieldSewParams G axes gridDepth).Valid) (q : (packHistory bottom M.epoch T).Index)

local notation "state" => Subtype.val (ProfileSum.term (packHistory bottom (Machine.epoch M) T) q)
local notation "network" => Pack.layout (flattenPack T (EnrichedOuter.State.pack state))
local notation "sewn" => enrichedSewnLayout G axes gridDepth order position count M bottom installed q
local notation "adapt" => enrichedSewnPrograms G axes gridDepth order position count M bottom installed oldPort hp q

/-- The signed adaptation stages the whole old program before the new cable and port bits. -/
theorem enrichedSewn_bank_size (old : Site.Programs network) (v : (sewn).Site) :
    (adapt old v).program.size = (old v).program.size + incoming sewn v := rfl

/-- The canonical wires, staged programs and supplied port bits in any region are
bounded by fifteen copies of the expanded records in the same pre-sewing region. -/
theorem enrichedSewn_region_capacity {C : Type} (old : Site.Programs network) (cell : (network).Site → C) (c : C) :
    guessedSize sewn cell c + siteSize sewn cell c (fun v => (adapt old v).program.size) + suppliedSize sewn cell c ≤
      15 * localRecords network true old.bankFields.prior old.bankFields.payload (fun v => cell v = c) := by
  let data : RecordData (state).pack.layout := ⟨old.bankFields.prior, old.bankFields.payload⟩
  let test := fun v => cell v = c
  have stage := staged_sewn_le sewn data.prior data.payload cell c (fun v => (old v).program.size)
  have retained := program_sizes_le network old test
  have grouped := enrichedSewn_records G axes gridDepth order position count M bottom installed hp.block hp.small q true data test
  change localRecords sewn true data.prior data.payload test ≤ 7 * localRecords network true data.prior data.payload test at grouped
  change testedWidth (fun v => (old v).program.size) test ≤ localRecords network true data.prior data.payload test at retained
  exact stage.trans ((Nat.add_le_add retained (Nat.mul_le_mul_left 2 grouped)).trans_eq (by ring))

variable (rows : ∀ j hj, (M j hj).F.SiteRows) (number : e.Entry → ℕ) (base : Site.Programs bottom.val.pack.layout)
local notation3 (prettyPrint := false) "prior" => M.terminalPrivatePrograms rows number bottom base q
local notation3 (prettyPrint := false) "result" => adapt prior

/-- Every coded terminal tile holds at most fifteen times the propagated bottom
budget, and this also bounds each adapted signed site's complete extent. -/
theorem enrichedSewn_address_capacity {C : Type} (code : (Epoch.Cube D → Deck (depth S start T+1)) ≃ C)
    (B : ℕ) (baseCap : SiteCap bottom.val.route base.bankFields true B) :
    let cell := fun v => code (reduceMove (depth S start T) ((state).route.origin v))
    let cap := 15 * (S.publicProgramFactor^T * B)
    (∀ c, guessedSize sewn cell c + siteSize sewn cell c (fun v => (result v).program.size) +
      suppliedSize sewn cell c ≤ cap) ∧ ∀ v, (result v).program.size ≤ cap := by
  intro cell cap
  have raw := M.terminalPrivatePrograms_bankCap rows number bottom base true B baseCap q
  have cellCap (c : C) : localRecords network true (prior).bankFields.prior (prior).bankFields.payload
      (fun v => cell v = c) ≤ S.publicProgramFactor^T * B := by
    have eq : (fun v : (network).Site => cell v = c) =
        (fun v => reduceMove (depth S start T) ((state).route.origin v) = code.symm c) := by
      funext v
      exact propext code.eq_symm_apply.symm
    have charge := congrArg (localRecords network true (prior).bankFields.prior (prior).bankFields.payload) eq
    exact charge.le.trans ((Nat.le_add_left _ 1).trans (raw (code.symm c)))
  have cells (c : C) := (enrichedSewn_region_capacity G axes gridDepth order position count M bottom installed oldPort hp q
    (prior) cell c).trans (Nat.mul_le_mul_left 15 (cellCap c))
  exact ⟨cells, fun v => (size_le_owner sewn cell (fun u => (result u).program.size) v).trans (cells (cell v))⟩

/-- At a word width accommodating the propagated bound, every signed bank and
every individual staging extent has a representable address. -/
theorem enrichedSewn_address_room {C : Type} (code : (Epoch.Cube D → Deck (depth S start T+1)) ≃ C)
    (B w₀ : ℕ) (baseCap : SiteCap bottom.val.route base.bankFields true B)
    (fits : 15 * (S.publicProgramFactor^T * B) < 2^w₀) :
    let cell := fun v => code (reduceMove (depth S start T) ((state).route.origin v))
    (∀ c, guessedSize sewn cell c + siteSize sewn cell c (fun v => (result v).program.size) +
      suppliedSize sewn cell c < 2^w₀) ∧ ∀ v, (result v).program.size < 2^w₀ := by
  intro cell
  have cap := enrichedSewn_address_capacity G axes gridDepth order position count M bottom installed oldPort hp q
    rows number base code B baseCap
  exact ⟨fun c => (cap.1 c).trans_lt fits, fun v => (cap.2 v).trans_lt fits⟩

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
